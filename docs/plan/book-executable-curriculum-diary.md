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

## 2026-08-30 — addition, memory, and branch flagship routes

Added the next three concrete A0 evidence producers and replay checkers:

- exhaustive width-8 addition checks all 65,536 operand pairs against an
  independent arithmetic oracle for the destination, Z/N/C/V, PC=4, preserved
  sources, and running outcome;
- a 16-bit memory trace stores `0xabcd` at unaligned address 1, observes bytes
  `[0xcd, 0xab]`, loads the same word, and separately establishes that an
  out-of-range store traps without a partial write;
- conditional-branch traces record taken PCs `[0,8,8]` and untaken PCs
  `[0,4,4]`, including the repaired rule that halt preserves its PC.

Each route has a distinct firing mutation. Addition reads r3 instead of the
declared r2 destination. Memory reverses the two stored bytes. Branching uses
the current PC instead of sequential PC as its relative-target base. All three
controls exit nonzero with `semantic-mismatch`, while the positive CLI routes
reproduce their reports. The evidence crate now has six passing route tests
under strict all-target Clippy.

Addition earns the `computation` class only for width 8. Memory and branch earn
the `trace` class only for their printed inputs. None is a symbolic theorem,
independent certificate, or kernel reconstruction.

## 2026-08-30 — bounded exhaustion versus returned continuation

Auditing `OP.a0.run` against Chapter 5 found an API-level omission. The
concrete runner distinguished halt, trap, and bound exhaustion, but it had no
way to return a deliberately short running prefix without calling that result
bound exhaustion. The book treats the caller's continuation decision as
metadata, distinct from both architectural outcome and verification budget.

Added `StopReason::PrefixReturned` and `run_prefix`. Both bounded execution and
prefix return share one private transition loop, so classification cannot
silently change fetch/decode/step behavior. Reaching halt or trap still
overrides the requested running-prefix label. Tests cover the zero-step bound,
terminal override, a running prefix, resumption from its final state, and the
concatenation law: prefixes of lengths two and three equal one prefix of length
five after removing the duplicated join state.

The semantic package is now version 3 and declares `returned-prefix`. Added a
recomputed runner-classification report covering halted, trapped,
bound-exhausted, and prefix-returned results. Its negative control falsely
labels the running prefix as halted and is rejected with `semantic-mismatch`.
Strict Clippy passes; `axeyum-machine` has 20 passing integration tests and the
evidence crate has seven passing route/control tests. This is concrete trace
evidence, not a termination proof.

## 2026-08-30 — canonical A0 encoding and exhaustive decoder round trip

The Chapter 6 audit found that A0 had a strict decoder but no encoder. Without
one canonical encoder, the promised structured-instruction round trip and
encoding injectivity check could not run. Added `encode` to the same Rust
semantic authority. It covers all seventeen instruction families and rejects
register indices outside r0 through r7 instead of truncating them into fields.

The decoder evidence route enumerates all 41,409 legal structured A0
instructions: every register combination, every signed eight-bit immediate or
offset, every branch condition, and halt. All 41,409 canonical encodings are
distinct, and decoding each returns the exact input instruction. The route
also rejects 82,818 high-reserved-bit mutations, eight targeted unused-field
mutations, and an unknown opcode. Its load-bearing control accepts one reserved
mutation; recomputation falls to 82,817 rejections and exits with
`semantic-mismatch`.

The semantic package is now version 4 and declares the encoder. Strict Clippy
passes; the machine crate has 21 integration tests and the evidence crate has
eight route/control tests. The result is an exhaustive finite computation over
the structured legal instruction domain. It does not enumerate all 2^32 byte
strings or prove a symbolic decoder theorem.

## 2026-08-30 — complete A0 step-family and footprint coverage

Added a source-bound coverage route for the remainder of `OP.a0.step`. It
executes one deliberately nondegenerate instance of each of the seventeen
instruction families from encoded bytes, compares every dynamic read and write
footprint with an independent expected row, and checks that the complete
successor changes only declared writable components. Four controls reach the
misaligned-PC, incomplete-fetch, illegal-encoding, and data-range traps. Halted
and every trapped state are checked for terminal stuttering.

The load-bearing mutation adds an undeclared write to r7 after a move. The
frame result changes from true to false, and the recorded report is rejected
with `semantic-mismatch`. Direct CLI production and replay pass with seventeen
families, seventeen exact effect rows, four trap classes, terminal stuttering,
and frame checks. The evidence crate now has nine route/control tests under
strict Clippy.

The control was then widened into a diagnostic suite matching the chapter's
explicit requirements. It independently checks the hidden r7 write, removal
of the addition condition update, and replacement of sequential `pc+4` with
`pc+1`. The suite returns `semantic-mismatch` only after all three mutated
recomputations differ from the recorded report; an unexpectedly accepted
mutation has the separate `control-failure` category.

This route establishes implementation coverage, not universal semantic
correctness for every possible input state. The exhaustive decoder and
width-eight addition routes provide stronger finite claims in their stated
domains; symbolic and kernel routes remain separate work.

## 2026-08-30 — one addition definition for execution and symbolic evidence

The symbolic-proof audit rejected a tempting but invalid shortcut: writing a
separate bit-vector formula that merely resembles the Rust executor. Such a
certificate would prove the formula, not the instruction semantics used by the
book. A0 addition now calls a public, domain-parametric `addition` definition.
The concrete executor instantiates its primitive word and condition operations
with A0 `Word` and `bool`; the forthcoming evidence route will instantiate the
same orchestration with Axeyum IR terms.

The `AdditionDomain` implementation is an explicit trust boundary. Sharing the
orchestration prevents drift in which result and which four conditions the
operation produces, but it does not by itself prove that a symbolic primitive
faithfully represents its concrete counterpart. The certificate route must
therefore bind its Boolean terms to the saved DIMACS, recheck DRAT and LRAT,
and replay a satisfiable mutated formula through concrete execution. The
existing 21 machine tests and nine evidence route/control tests pass after the
refactor, including exhaustive width-eight concrete flags.

The certificate route is now implemented. For each supported A0 width (8, 16,
24, 32, 40, 48, 56, and 64), the evidence producer instantiates that shared
addition definition with Axeyum IR terms and asks whether any operand pair
differs from the architecture reference predicates. The saved artifact carries
the deterministic DIMACS plus DRAT and LRAT refutations. Replay reconstructs
the Boolean term from source, compares its rendered-term digest, regenerates
the term-to-CNF binding, checks LRAT, and also checks the published DRAT. A
certificate with malformed DRAT is rejected in the end-to-end test.

The negative control inverts the derived carry bit. The QF_BV route reports the
mutated query satisfiable. The evidence producer then independently enumerates
the complete 65,536-pair width-eight term domain with the Axeyum IR evaluator,
obtains the deterministic witness `(0, 0)`, and replays encoded A0 `add` through
the concrete `step` function. Concrete carry is false and mutated carry true;
the destination result also replays. This establishes a real counterexample
path rather than merely checking that the proof producer declined.

The claim remains fixed-width and route-specific: eight finite QF_BV theorems,
not an induction theorem over arbitrary widths. The symbolic adapter's mapping
to IR primitives and Axeyum's term-to-CNF lowering remain explicit trusted
reductions. LRAT checks the clausal refutation; it does not erase those
boundaries.

Strict Clippy also exposed that the default QF_BV profile compiled
`export_qf_bv_unsat_proof_with_progress` without exporting it. The solver
facade now exports the progress-aware function from both its canonical proof
namespace and crate-root compatibility surface, removing the downstream
dead-code failure instead of suppressing it. The semantic package is version 6
and declares `domain-parametric-addition`.

## 2026-08-30 — complete the reusable A0 word-operation contract

Auditing the book's still-open `OP.a0.word-package` obligation against the
compiled crate found a real partial implementation. `Word` already supplied
construction, modular reduction, unsigned and signed readings, high-bit
inspection, and little-endian split/join. It did not supply the explicit zero
extension, sign extension, or truncation operations that Chapters 1 and 3
promise to use as reusable semantic primitives.

Added `Word::zero_extend`, `Word::sign_extend`, and `Word::truncate`. Each
accepts only the eight supported byte-multiple widths. Widening operations
reject narrowing; truncation rejects widening; identity conversions are legal.
The error retains both source and target widths. Direct tests cover positive
and negative extension, low-bit truncation, identity cases, invalid direction,
and an unsupported target width.

The new source-bound word-package report checks 65,822 source words and
2,106,910 individual operation results. It exhaustively enumerates all 8- and
16-bit words, applies every legal widening target, truncates each extension
back to its source width, and checks signed and unsigned readings plus byte
split/join against independent integer oracles. Five boundary vectors at each
larger supported width cover zero, one, the largest positive signed value, the
smallest negative signed value, and the all-ones word. Invalid-direction
controls are included in the report.

The load-bearing mutation implements zero extension by calling sign extension.
It changes the report digest and the checker exits nonzero with
`semantic-mismatch`. The positive CLI producer and checker pass directly.
`axeyum-machine` now has 22 integration tests; the evidence crate adds a tenth
route/control test; strict all-target Clippy passes for both crates.

This is a finite implementation audit, not an induction theorem over arbitrary
widths. Exhaustiveness applies only to the complete 8- and 16-bit value
domains. Larger widths have named boundary coverage. The compiled source digest
binds the report to the implementation, and the semantic package advances to
version 7; it does not independently prove the Rust compiler or integer
oracles.

## 2026-08-30 — canonical complete-state artifact boundary

The next book audit found that `OP.a0.state-memory` mixed three different
claims. Concrete state, observation, finite memory, range checking, and trapped
effects already execute. Canonical serialization of arbitrary complete states
did not exist, while the universal memory-frame theorem is a separate symbolic
claim and must not be inferred from either implementation tests or a codec.

Added a dependency-free canonical binary codec to `axeyum-machine`. The format
fixes magic, version, architectural width, full finite-memory length and bytes,
register order, fixed-width little-endian integers, condition-bit positions,
outcome tags, and all four trap payloads. Encoding rejects register or PC width
drift, out-of-width trap locations, and a data-range trap whose recorded memory
length differs from the complete state. Decoding rejects bad magic or version,
unsupported widths, truncated fields, out-of-width register/PC/trap values,
reserved condition bits, unknown outcome and trap tags, inconsistent trap
memory length, and trailing bytes.

Direct tests round-trip and byte-for-byte re-encode running, halted, and all
four trapped states. A second test checks ten independent malformed encodings
and malformed in-memory states. The source-bound report expands this to all
eight supported widths and all six outcome forms: 48 complete canonical state
round trips plus ten malformed encodings. Its load-bearing mutation accepts one
trailing byte. Recomputed evidence then changes from ten rejected mutations to
nine and exits with `semantic-mismatch`.

The positive producer and checker pass directly. `axeyum-machine` has 24
integration tests, the evidence crate has twelve route/control tests across its
test binaries, and strict all-target Clippy passes. The semantic package moves
to version 8 and declares `canonical-state-codec`.

This route establishes a canonical artifact representation for the named test
population and rejects the declared malformed classes. It is not exhaustive
over all possible states, and it does not establish the still-separate
universal memory-frame theorem or a Python projection.

## 2026-08-30 — remove the dense-memory shortcut

Reviewing the new codec against Chapter 4 exposed a semantic mismatch that the
existing dense examples could not detect. The book defines memory as an
arbitrary finite map from word addresses to bytes. A valid multi-byte range is
checked address by address after modular word addition, so it may wrap and the
domain may contain holes. The first Rust implementation used a zero-based
`Vec<u8>` and treated `start + byte_count <= len` as validity. That implements
only dense initial-segment memory and did not fulfill the printed definition.

Replaced the representation with a canonically sorted finite address-byte map.
`Memory::from_entries` admits sparse domains and rejects duplicate addresses;
`State::new` rejects addresses outside the declared word width. Load and store
now enumerate every modular word address in the requested range, require every
one to be present, and collect the complete address vector before writing. A
failed store therefore cannot partially commit. The existing dense
constructors remain convenience projections onto addresses `0..len`.

The canonical state codec now writes the full sorted address and byte for each
memory entry, so stored zero remains distinct from absence and sparse domains
round-trip without relying on host-map iteration order. Observation and
evidence digests likewise consume ordered address-byte pairs. Frame checking
compares complete domains and handles wrapped write footprints.

A direct width-16 test stores `0xabcd` at address `65535` into the mapped pair
`{65535, 0}`, confirming bytes `cd` and `ab` across wrap while preserving an
unrelated mapped address. Removing address zero makes the same store trap with
the entire sparse memory unchanged. Duplicate addresses and an out-of-width
domain entry are independently rejected. All 25 machine integration tests and
the complete evidence test set pass; strict all-target Clippy passes.

This repair advances the semantic package to version 9. It establishes the
executable finite-map behavior and canonical representation. The universal
symbolic memory-frame theorem remains a separate open claim.

The book-facing memory report now binds the repair rather than relying on the
crate test alone. In addition to its existing dense unaligned round trip and
boundary trap, it records wrapped addresses `[65535, 0]`, stored bytes
`[0xcd, 0xab]`, the sparse-hole trap, and complete-map preservation. The
existing reversed-byte-order mutation remains load-bearing and rejects the
widened report.

## 2026-08-30 — version the widened memory evidence contract

The sparse-memory repair added wrapped addresses, sparse stored bytes, a
missing-address trap, and complete-map preservation to the public memory
report. Leaving that materially wider JSON contract under
`axeyum.a0.memory-trace.v1` would make two different report shapes claim the
same schema identity. Advanced the report schema to
`axeyum.a0.memory-trace.v2`. This changes no machine semantics; it makes the
artifact boundary accurately identify the report that producers, checkers,
manifests, and the book exchange.

## 2026-08-30 — source-derived symbolic A0 memory-frame theorem

The concrete sparse traces could not establish the universal frame claim. A
second handwritten solver formula would not close that gap either: it could
agree with the book while bypassing the executable load/store implementation.
Refactored A0 memory access around a public `MemoryDomain` boundary, parallel
to the existing `AdditionDomain`. One shared `memory_load` and `memory_store`
orchestration now owns modular address enumeration, per-address presence,
little-endian split/join, validity conjunction, tentative writes, and the
all-or-nothing choice between the updated and complete original memories. The
ordinary `Memory::load` and `Memory::store` paths instantiate that definition
with concrete words, bytes, Booleans, and the canonical sparse map.

Added a symbolic instantiation using a word-indexed byte array and a separate
one-bit presence array. For each of the eight supported widths, the theorem
uses arbitrary old arrays, base address, stored word, and probe address. It
checks that load validity is exactly the conjunction of the addressed presence
bits; successful load reconstructs the selected bytes in little-endian order;
store validity is the same predicate; an arbitrary successor probe contains
the corresponding source byte exactly when the valid write footprint contains
it and otherwise retains the old byte; a trapped store retains the old byte;
and store preserves the complete presence domain. Because the probe is an
arbitrary word, the pointwise result establishes complete-memory equality and
the store frame law without using unsupported array equality.

Each width saves the exact rendered-assertion digest, deterministic
array-eliminated DIMACS, DRAT, LRAT, and the number of re-derived select
congruence constraints. The checker rebuilds terms from the compiled source,
re-runs the array elimination, re-derives its congruence witness, confirms the
saved DIMACS, and independently replays DRAT and LRAT. All eight widths pass.
The largest width has 72 select-congruence constraints; the complete report is
about 384 KiB.

The load-bearing mutation commits the tentative map even when a later address
is absent. Its width-16 symbolic negation is satisfiable. A concrete encoded A0
store at address 65,535 over the sparse domain containing only that first
address traps and preserves byte zero, while the mutated orchestration leaves
`0xcd`. Thus the negative control exercises the same atomic-failure clause as
the theorem rather than merely corrupting unrelated report metadata.

This proves the A0 word-sized load/store frame theorem for the eight declared
finite bit-vector widths and arbitrary finite-domain characteristic arrays. It
does not prove an induction theorem for widths outside A0, instruction decode,
or any RV64I or x86-64 memory behavior. The semantic package advances to
version 10 and declares `domain-parametric-memory`.

## 2026-08-30 — first source-pinned RV64I decoder and step slice

The book's seven RV64I listings reduce to twelve base forms: `ADDI`, `ADD`,
`SUB`, `OR`, `XOR`, `LD`, `SD`, `BEQ`, `BNE`, `BGE`, `JAL`, and `JALR`.
Pinned them to the official RISC-V Unprivileged Architecture release
20260120, RV64I version 2.1. The official 696-page PDF retrieved from
`docs.riscv.org` on 2026-08-30 is 4,580,174 bytes with SHA-256
`06bb3c23074f72060a0ec061a80933af948cae7ceafdcd9d1fe177b05fd150bc`.
The selected profile excludes compressed instructions and every extension.
It requires four-byte instruction addresses and naturally aligned
doubleword accesses; missing data bytes, misaligned data, incomplete fetch,
illegal words, and misaligned taken targets remain distinct traps.

Added `axeyum-machine::rv64` with strict decode and canonical encode for all
twelve forms, complete 32-register state with architectural `x0`, finite
little-endian memory, immutable code, PC-relative branches and `JAL`, low-bit
clearing for `JALR`, link writes, atomic aligned `LD`/`SD`, and terminal trap
stuttering. The memory path reuses the source-derived domain-parametric A0
load/store orchestration with an RV64 doubleword adapter rather than creating a
second range and byte-order loop.

Seven direct tests bind the source identity and exact form set; round-trip
known encodings from Chapters 6 and 12; decode every word in the nine-row XOR
table from Chapter 15; exercise `x0`, arithmetic, and branch-PC rules; test
little-endian aligned load/store plus sparse access and alignment traps; test
link, target, and fault-before-link behavior; and check a canonical
refinement-facing projection with sorted registers and the complete sparse
memory domain. Strict Clippy passes.

This code slice does not yet close either RV64 obligation. The book-facing
source manifest, independently replayed decoder/step evidence, mutation suite,
and pinned Axeyum revision still need to land and run.

## 2026-08-30 — replayable RV64I source and execution evidence

Added two book-facing evidence producers and checkers. The source route emits
the official document URL, release 20260120, PDF digest, byte and page counts,
RV64I version 2.1, the exact twelve selected forms, the compiled implementation
digest, profile choices, and exclusions. Its negative control changes the
official-source digest and the checker rejects the result.

The decoder/step route decodes and canonically re-encodes thirteen words printed
in Chapters 6, 12, and 15, including every word of the XOR program. It also
executes each of the twelve selected forms as a real transition and checks the
form's architectural effect. The same executor runs the complete nine-word XOR
program on empty, singleton, and three-word inputs and obtains `0`,
`0x0123456789abcdef`, and `7`. Separate checks exercise `x0`, canonical state
projection, five distinct trap classes, and three load-bearing semantic
mutations.

During review, the first draft's `forms_executed` count was found to cover only
encode/decode round trips. That was not a truthful execution claim. The final
route now steps all twelve forms and checks register, memory, PC, link, or
branch effects as appropriate. The branch-base control likewise executes the
book's taken `BNE` at PC 28 and observes target 12 before comparing it with the
mutated sequential-PC target 16; it no longer relies on a handwritten target
constant alone.

The focused machine and evidence run passes 47 integration tests, including the
two new end-to-end RV64 route tests. Strict all-target Clippy passes. Direct CLI
replay accepts both generated reports; the source-digest and sequential-PC
controls each exit nonzero with `semantic-mismatch`. The implementation landed
as `eac21f4d4`. This closes the Axeyum producer/checker side, but the two book
objects remain open until their manifests, saved reports, wrapper checks, and
`make check-run` bindings land in the book repository.

## 2026-08-30 — first source-pinned x86-64 decoder and step slice

The six x86-64 listings in the manuscript require more than the XOR loop. The
complete printed form set includes 32-bit XOR and immediate MOV, 64-bit TEST,
three short conditions, a 64-bit memory-source XOR, sign-extended immediate
ADD and SUB, register MOV and ADD, NEG, LEA with an eight-bit displacement,
PUSH, POP, direct near CALL, and RET. The implementation covers all seventeen
of those selected form families rather than reducing the slice to the case
study alone.

Pinned the slice to Intel's combined Volume 2 instruction reference, order
number 325383-092US, June 2026. The official PDF retrieved from Intel on
2026-08-30 is 11,258,123 bytes and 2,573 pages with SHA-256
`db01e5918a710c16487e27a9e71a19af201f39b3311c55550559baaf0805160b`.
The slice accepts only the exact legacy and REX.W shapes used by the book. It
excludes extended registers, SIB and RIP-relative addressing, longer
displacements, near conditional jumps, non-integer state, privileged forms,
and every vector or newer prefix family.

Added `axeyum-machine::x64` with variable-length decode and canonical encode,
the low eight general-purpose registers, RIP, finite byte memory, running or
trapped outcome, and CF, PF, AF, ZF, SF, and OF. Flags can be explicitly
undefined; logical XOR and TEST therefore do not invent an AF value. A
32-bit destination write clears the upper half. Short branches use the address
after the decoded instruction. Arithmetic computes all six selected flags.
Memory-source XOR permits unaligned byte-map accesses, while missing bytes
trap without a partial effect.

The stack and control forms expose their implicit behavior. PUSH, CALL, POP,
and RET read or write the finite stack memory and update RSP in architectural
order. CALL pushes the following RIP before applying its signed relative
displacement. RET reads the continuation before advancing RSP. A review found
and fixed the special POP-to-RSP write order even though the book prints only
`pop rbx`; the accepted form family must be correct for every register it
admits.

Eight direct tests cover source identity; canonical round trips for every
selected family; exact absolute-value and write-zero bytes; the complete
21-byte XOR program on empty, singleton, and three-word inputs; EAX clearing,
defined and undefined flags, and following-RIP branch bases; stack control and
atomic faults; decode traps and canonical projection; and executable witnesses
for all six manuscript listings, including leaf and non-leaf procedures.
Thirty-two existing A0 and RV64 tests remain green. Strict all-target Clippy
passes. The semantic slice landed as `3c5d2cafb`.

This closes the first Axeyum semantic layer, not the two x86-64 book
obligations. The source report, independently replayed decoder/step report,
length and implicit-effect mutations, pinned manifest, and book bindings still
need to land and pass `make check-run`.

## 2026-08-30 — replayable x86-64 source and execution evidence

Added source-pin and decoder/step evidence producers for the complete selected
x86-64 slice. The source report records Intel order number 325383-092US, June
2026, official URL, PDF digest, byte and page counts, all seventeen form
families, the compiled semantic-source digest, profile choices, and exclusions.
Changing one nibble of the official PDF digest produces the required
`semantic-mismatch`.

The execution report binds twenty-eight manuscript or resolved teaching-fixture
encodings. It checks each decoded length and canonical re-encoding, then runs
the six manuscript programs. The 21-byte XOR routine returns `0`,
`0x0123456789abcdef`, and `7`; the count loop reaches zero; the leaf returns
42; both signs of the absolute-value fixture produce 7; and the non-leaf
fixture returns 7 while restoring RBX and the expected stack position. The two
write-zero forms both execute, produce the same RAX value, and retain their
different flag effects. Taken and untaken inputs ensure that all three selected
short conditions execute rather than merely decode.

The report separately checks canonical state projection and three trap classes:
incomplete variable-length fetch, illegal instruction, and missing data bytes.
Four load-bearing mutations are distinguished: using instruction RIP instead
of following RIP as a short-branch base, failing to clear the upper half on an
EAX write, treating logical AF as defined-clear, and omitting CALL's implicit
stack write or RSP change. The branch mutation is the external negative-control
command. It executes the printed `jne` at address 18 with displacement -13;
the correct following-RIP target is 7, while the mutated instruction-RIP target
is 5.

The focused machine and evidence suites pass 55 integration tests. Strict
all-target Clippy passes. Direct CLI generation and replay accept both reports;
both negative controls exit nonzero with `semantic-mismatch`. The evidence
routes landed as `5ad3bbfcd`. The Axeyum half is complete, but the book objects
remain open until their manifests, saved reports, digests, prose bindings, and
full `make check-run` replay land.

## 2026-08-30 — first reader-facing PyO3 machine projection

Started the Python lesson surface at the lowest reusable boundary: A0 words.
Added `axeyum.machine.a0.Word` as a direct wrapper around
`axeyum_machine::a0::Word`; construction, signed and unsigned readings, high
bit, little-endian bytes, zero extension, sign extension, and truncation all
delegate to the Rust value. Python does not carry duplicate bit arithmetic.
The constructor preserves the Rust contract and reduces an admitted `u64`
modulo the selected width; unsupported widths and wrong-direction conversions
raise `ValueError` with messages supplied by a new `Display` implementation on
`A0Error`.

Added the normal `axeyum.machine` forwarding module, nested dotted imports,
generated stubs, and seven direct Python controls. The audit caught two
interface defects before publication. PyO3 exposes `Vec<u8>` as Python
`bytes`, while the generated stub claimed `list[int]`; the binding now returns
`PyBytes` explicitly so runtime and static type agree. Stub regeneration also
revealed that the existing runtime constant
`producers.MAX_RETRIEVED_DECLARATIONS` had no generator declaration. Added the
missing module-variable record instead of preserving a hand-written stub.

Focused evidence passes: 26 A0, 7 RV64, and 8 x86 machine tests; 8 native
binding tests; 24 machine/import Python tests; strict Clippy for
`axeyum-machine` and `axeyum-py`; generated-stub/runtime comparison; the
94.7-percent typed-stub gate; `mypy.stubtest`; the type-diagnostic budget;
Ruff lint; and Ruff formatting.

The aggregate `just py-check` is not green for reasons reproduced outside the
new machine tests. `test_an_unresolvable_export_is_recorded_as_a_retrieval_miss`
uses fact `F:ml430-int-fib-add-181b6a2c`, which is no longer in the current
eligible population. Separately,
`test_agent_tools.py::test_every_declared_prelude_builds` deterministically
segfaults by itself in `agent/tools.py::_kernel_for` while building every
prelude. These are full-gate blockers, not evidence against the focused word
projection, and must be repaired before this lane can claim the complete
Python gate.

This slice is intentionally not called the Python machine interface complete.
States, memory, instructions, decode/encode, step, trace, RV64, x86-64, and the
cross-machine relation remain unbound.

## 2026-08-30 — Python full-gate crash and stale-control repair

Investigated the aggregate Python failures rather than excluding the agent
tests. The prelude crash was reproducible without pytest: a fresh interpreter
built `nat`, `int`, `logic`, and `rat`, then `build_creal_prelude()` exited 139;
a second fresh interpreter did the same in `build_complex_prelude()`. Both had
outgrown the main thread's 8 MB stack. The existing `cpoint` binding already
documented and solved the same failure by building on a scoped 64 MB thread.
Moved `creal` and `complex` across that boundary, retaining GIL release, panic
conversion, and the returned kernel. The seven-prelude census now passes in
115.75 seconds instead of killing CPython.

The retrieval-miss control named a fact that had left the live eligible
population. It now derives an eligible fact for which the authoritative export
resolver returns `ExportUnavailable`, and fails explicitly if the corpus no
longer contains such a control case. The focused test reaches the intended
`retrieval-miss` outcome again.

After those repairs, the complete suite runs to completion rather than
segfaulting: 1,846 pass and 34 skip. Nine failures remain in unrelated,
already-drifted knowledge/autogenesis checks: two bounded-application census
expectations, one changed dependency count, three parsers that assume an older
validator output grammar, one clean fixture rejected by the current validator,
one nursery population mismatch, and one standard-library-only scripts rule
breached by a tracked generator. This lane does not reinterpret those nine as
machine-binding failures, but the aggregate `just py-check` remains red until
their owning artifacts are reconciled.

Those nine results came from the lane's superseded base. Before integration,
`origin/main` was fetched and found 1,825 commits ahead; the four lane commits
were rebased cleanly onto that authoritative head. The current-base gates must
therefore be rerun before retaining or clearing any of the nine diagnoses.

The current-base rerun completed in 563.08 seconds with the same exact result:
1,846 passed, 34 skipped, and the nine named knowledge/autogenesis failures.
The machine projection, prelude crash repair, and retrieval control all passed
inside that run; the aggregate gate remains accurately red.

## 2026-08-30 — complete reader-facing A0 Python execution surface

Expanded the first word-only projection into the complete A0 surface needed by
a reader to construct and execute the teaching machine. The Python layer now
wraps the Rust `Conditions`, finite dense or sparse `Memory`, immutable
`Program`, categorized `Trap`, `Outcome`, canonical `State`, all seventeen
typed `Instruction` families, and bounded `Trace`. `step`, `run`, and
`run_prefix` delegate directly to `axeyum_machine::a0`; no instruction
semantics or state transition is reimplemented in Python.

The first draft did not compile under current PyO3 because it expanded helper
macros inside a `#[pymethods]` block, a pattern PyO3 now rejects. Replaced the
macro-generated arithmetic and shift factories with explicit methods. Every
factory now runs the Rust canonical encoder before returning, so an invalid
register is rejected at construction rather than surviving until a later
`encode()`. Added explicit PyO3 object-extraction policy to every cloned class,
borrowed trap inspection instead of moving variants, and exposed instruction
operands so decoded bytes are inspectable rather than identified only by an
opcode-family string.

Added six end-to-end Python controls beyond the existing seven word controls.
They cover dense and sparse memories plus duplicate rejection; immutable state
updates, width validation, and canonical state-codec replay; canonical
encode/decode for all seventeen instruction families and malformed factories;
the exact overflowing eight-bit addition transition including destination,
frame, PC, and four flags; little-endian store/load plus a trapped store with
no partial write; and the distinct `bound-exhausted`, `prefix-returned`, and
`halted` trace outcomes including terminal stuttering.

The built editable extension passes all 13 machine tests. Strict all-target,
all-feature Clippy passes for `axeyum-py`. Generated stubs describe the new
surface and agree with the imported extension: 25 modules, 1,783 symbols, five
intentional aliases, and 301 synthesized dunders. The typed-stub gate reports
1,588 typed parameters and 131 explicitly allowlisted `Any` uses; `stubtest`
passes; the Python type check retains its four-diagnostic budget with its
control firing; and Ruff lint and formatting pass for the expanded test file.
The implementation and generated reader contract landed as `4e93f9d62`.

This closes the A0 portion of the reader-facing Python machine interface. It
does not close the whole Python plan: RV64, x86-64, cross-machine relations,
book-example bindings, clean-checkout installation, and the nine aggregate
knowledge/autogenesis failures remain open.

## 2026-08-30 — preserve semantic identity across error presentation

The first full book replay after binding the Chapter 6 Python example exposed
a failure that the focused Python gates could not see. All twelve A0 producers
exited with `semantic-package-mismatch`, while the four real-ISA routes passed.
The pinned A0 package expected source SHA-256
`6c57ccf27e25f6ec1c24f25c32599715bd9f725ff8dd03ff2da1f4d8354cb79a`;
the current `a0.rs` hashed to
`6659f24e1710b4feebcc6f56d12565f39490e9cbd47b946522ee57c6cade701d`.

The only difference from the pinned semantic source was the reader-facing
`Display` and `Error` implementation added for Python exceptions. No word,
memory, decode, step, or trace rule had changed. Regenerating twelve semantic
artifacts would therefore have assigned a new semantic identity to a message
change. Instead, moved that presentation implementation into the private
`a0_error` module and kept the public error type in `a0.rs`. The semantic
source now reproduces the exact pinned digest while Python retains the same
messages and Rust error trait.

Twenty-six direct A0 tests pass, including the reader-facing message controls.
Strict all-target, all-feature Clippy passes for `axeyum-machine` and
`axeyum-py`. Most importantly, the book's live replay now accepts all sixteen
routes again: twelve A0, two RV64, and two x86-64, each with its negative
control. The boundary repair landed as `4548f3dda`.

## 2026-08-30 — reader-facing RV64I Python projection

Added `axeyum.machine.rv64` as a direct projection of the source-pinned Rust
teaching slice. It exposes the official source release, source digest, RV64I
version, exact twelve-form selection, typed constructors for every admitted
form, canonical encode/decode, immutable program bytes, complete integer state,
finite A0 memory, categorized outcomes and traps, canonical state projection,
and one-step execution. The normal forwarding module and dotted native import
both expose the same objects.

Every instruction constructor validates through the Rust canonical encoder.
Register access checks `x0..x31` before calling the underlying state method, so
an invalid Python index becomes `ValueError` instead of reaching a Rust array
panic. Immutable `with_register` preserves the architectural x0 rule. Python
does not implement instruction behavior, fetch, target arithmetic, memory
access, or traps; `step` delegates to `axeyum_machine::rv64::step`.

Four reader-facing test groups cover all twelve constructor/round-trip forms
and invalid operands; x0 plus the instruction-PC-relative branch base; aligned
little-endian store/load, canonical projection, duplicate rejection, and an
atomic missing-byte store; and the pinned source identity plus all five trap
classes with terminal stuttering. The existing seven native RV64 tests and
eight PyO3 library tests also pass. Strict all-target, all-feature Clippy
passes. Runtime/stub parity now covers 26 modules and 1,804 symbols; the typed
stub gate reaches 95.1 percent, `stubtest` passes, the existing type-diagnostic
budget remains unchanged, and Ruff lint and formatting pass.

This is a single-step concrete projection, matching the current Rust API. It
does not invent a Python-only runner. RV64 bounded traces, x86-64, instruction
effect sets, symbolic execution, and cross-machine relations remain open.
The implementation and generated reader contract landed as `3884b8d04`.

## 2026-08-30 — reader-facing x86-64 Python projection

Added `axeyum.machine.x64` as the direct projection of the source-pinned Intel
teaching slice. It exposes the pinned source revision and digest, the exact
seventeen selected form families, typed constructors for all fifteen Rust
instruction variants including the three admitted short conditions, variable-
length canonical encode/decode with consumed length, immutable program bytes,
six three-valued flags, complete state, finite memory, categorized traps,
canonical state projection, and one-step execution.

Instruction factories validate through the Rust canonical encoder. Short-jump
conditions accept a small documented spelling set and return one canonical
name. Flag values are `clear`, `set`, or `undefined`; the Python surface does
not collapse an architecturally undefined flag to false. Register reads and
immutable updates check the selected low-eight boundary before calling Rust.
All instruction behavior, variable-length fetch, following-RIP arithmetic,
partial-register behavior, implicit stack access, and trapping remain in
`axeyum_machine::x64::step`.

Four new reader test groups cover all seventeen selected forms and exact decode
lengths; EAX upper-half clearing, logical flag definitions, undefined AF, and
taken following-RIP-relative branches; CALL/RET continuation and RSP effects
plus atomic failed PUSH; and source identity, canonical projection, duplicate
rejection, incomplete fetch, illegal instruction, and terminal stuttering.
The eight native x86 tests still execute all six printed manuscript listings.
Eight PyO3 library tests also pass. Strict all-target, all-feature Clippy
passes. Runtime/stub parity now covers 27 modules and 1,828 symbols; typed-stub
coverage reaches 95.2 percent, `stubtest` passes, the type budget is unchanged,
and Ruff lint and formatting pass.

Like RV64, this is a complete selected single-step projection, not a new
Python-only runner. Real-ISA bounded trace types, instruction effect sets,
symbolic execution, and cross-machine relations remain open.
The implementation and generated reader contract landed as `ebcbfc618`.

## 2026-08-30 — first typed cross-machine relation and replay route

The executable machine layers made the next open book dependency precise:
Chapter 12 had three working absolute-value programs but no typed object that
said when their unequal states represented the same logical point. Added a
`cross_isa` semantic module that consumes the existing A0, RV64I, and x86-64
states and steps. It binds the exact bytes printed in the chapter and names the
entry, decision, optional negative update, and exit synchronization points.

The relation reports stable clauses for logical control, running outcomes,
A0-to-RV64 value agreement, A0-to-x86-64 value agreement, the A0 harness zero,
the shared signed predicate at the decision, and preservation of each entry
memory. A replay retains all three concrete states at every applicable point
and returns the first failed named clause. It implements no second instruction
semantics. Both the nonnegative stutter path and negative update path execute
through the original machine packages.

Added a source-bound evidence route over ten declared 64-bit boundary and
branch-shape inputs. The set includes zero, positive and negative witnesses,
both signed extrema, and mixed-bit patterns. Every case reaches all applicable
points and produces one common modular result. The report separately records
that the signed minimum is excluded from the positive mathematical-absolute-
value interpretation, although its modular result still agrees on all three
machines. This is a finite concrete computation, not a universal theorem over
all 64-bit words.

The load-bearing control changes the x86 signed jump from `jns` to `je` while
leaving the relation checker unchanged. Input seven then reaches x86 address 8
instead of the shared exit at 11, and the route rejects the trace at the exit
`ControlPoint` clause. Direct production and replay report ten passing cases
with result SHA-256
`75f1e5d688a694861ee4b397938174b5c122d64998155a9ce2c2f36598e7ad4d`;
the control exits nonzero with `semantic-mismatch`. Strict all-target Clippy
passes for both machine crates, and the direct relation tests cover the two
paths, signed boundaries, stable point order, first-failure diagnosis, replay,
and malformed-report rejection.

The first artifact-generation pass caught that `u64::MAX` and signed `-1`
named the same bit pattern, so the advertised ten cases contained only nine
distinct inputs. Replaced the duplicate with `0x8000000000000001` and added a
set-cardinality assertion. The digest above is from the corrected ten-distinct-
input report.

This implements the first concrete A0-to-RV64 and A0-to-x86-64 relation route.
The book object and artifact still need to bind it before the obligation can
move from open to computed. A universal symbolic simulation, the A0
equivalence/counterexample route, scalar minimality, and the complete XOR
three-machine case remain open.

## 2026-08-31 — finite A0 equivalence queries and decoded-model replay

Implemented the first semantics-backed A0 equivalence route around the exact
one-instruction pair used in Chapter 11: `movi r0,0` and `xor r0,r0,r0`. A
canonical query now binds both encoded programs, width, one-step bound,
precondition, observation, and complete finite input family. The checker
decodes both programs and executes the existing A0 step function for every
admitted state; it does not introduce a second instruction semantics.

The route runs four queries at width eight. Result-only equivalence checks all
4,096 combinations of `r0` and Z/N/C/V. A destination mutation writing `r1`
instead produces a canonical encoded-state witness whose first observed
difference is `r0`. Full-state equivalence without a condition premise also
produces a witness; deterministic minimization chooses an initial state with
Z and C set so carry is the only successor difference. The exact premise
Z=true and N=C=V=false then establishes full-state equality for all 256 `r0`
values in that restricted family.

Every counterexample stores the complete canonical initial state and both
complete successor states. The checker decodes the saved model, reruns the
encoded programs, and requires the same successors and first observation
difference. One control mutates the XOR destination and requires a replayed
`r0` witness. A second changes one byte of the saved initial-state model and
requires concrete replay to reject it. Direct production and checking pass;
both controls exit nonzero with `semantic-mismatch`. The report SHA-256 is
`1f7697bc7e06a98f9c16edd055376d2a8c0c0ed8e6ce6c6ef9b166d4ebf4dc06`.
Strict all-target Clippy and the focused route test pass.

The scope is deliberately exact. This is exhaustive evidence for the declared
width-eight state families, not a solver certificate, a theorem for all A0
widths, arbitrary memory, multi-instruction programs, or termination. It now
provides the executable equivalence and counterexample-replay substrate needed
by the first bounded scalar-minimality route. The book object and manifest
remain to be bound before `OP.rel.a0-equivalence` can move from open.

## 2026-08-31 — exhaustive bounded A0 scalar minimality

Implemented the first executable minimality route for the Chapter 13 `x + 2`
example. The candidate language is an exact six-instance alphabet: `mov r0,r0`,
`mov r0,r1`, and the four `add r0,rs1,rs2` combinations with each source drawn
from `r0` and the read-only resource register `r1 = 1`. Only `r0` is writable.
The cost is decoded instruction count, the maximum cost is two, and the
observation requires both the final `r0` value and running completion.

The executable A0 model supports byte-multiple widths, so this route exhausts
all 256 inputs at width eight rather than the manuscript's earlier informal
width-four sketch. It enumerates the complete syntax product at costs zero,
one, and two: 1, 6, and 36 candidates. Those strata contain 1, 5, and 11
distinct complete truth tables and respectively 0, 0, and 4 correct syntactic
candidates. The selected printed witness is two consecutive
`add r0,r0,r1` instructions. Its report stores the complete 256-entry truth
table and establishes minimum cost two within this declared language.

Two load-bearing controls fail as required. Replacing the second increment
with `add r0,r0,r0` produces a concrete mismatch at input one. Omitting the
last alphabet member changes both the canonical language digest and enumerated
stratum cardinality. The direct producer and checker agree on result SHA-256
`06a6550fdf29f7239d0355f8d25a271fb866c641f25452a76fa738e19ab12f30`;
the serialized report SHA-256 is
`268bc13e35e606637b5703ddde0ca7a563a39a658793453b930339b653d071ce`.
Strict all-target Clippy and the focused route test pass.

This is finite direct enumeration over one exact width-eight language. It is
not a solver certificate, a search over arbitrary A0 programs, a theorem for
all widths, or a minimality result for RV64I or x86-64. The book object and
manifest still need to bind the report before the chapter obligation can move
from open to computed.

## 2026-08-31 — complete concrete Chapter 15 three-machine XOR route

Audited the Chapter 15 A0, RV64I, and x86-64 XOR-reduction listings against the
current typed executors. Every printed form was already supported, including
A0 load, XOR, arithmetic, conditions, and halt; RV64I LD, XOR, ADDI, branches,
and JALR; and x86-64's fused memory-source XOR, arithmetic flags, short
branches, and RET. The missing layer was not another decoder. It was a typed
relation over the exact complete programs.

Added that relation without introducing a shared instruction semantics. It
binds the exact printed 44-, 36-, and 21-byte images and executes each through
its existing architecture-specific step function. Entry, loop-head,
after-combine, and terminal cut points retain all three complete states. Nine
stable clauses check control location, outcome class, harness input mapping,
prefix accumulator, pointer, remaining count, A0 helper constants, complete
memory frame, and architecture-specific halt or return convention. The x86
memory-source XOR remains one transition; the relation compares it with the
two A0 and RV64I load-plus-XOR transitions only after the logical combine.

The evidence report replays eight named cases: empty, zero, all ones, the high
bit, an endian-sensitive word, equal-word cancellation, overlapping one bits,
and a three-word mixture. List lengths range from zero through three. Every
case reaches all applicable cut points, agrees with the direct 64-bit XOR fold,
and preserves memory. Dynamic counts match the chapter formulas exactly:
A0 6+5n, RV64I 4+5n, and x86-64 4+4n. The harness rejects more than 96 words
before the data region can overlap the x86 return stack.

The load-bearing control changes only RV64I's pointer increment from eight to
one. The two-word overlapping-bits case rejects it at the second loop head in
the pointer clause. Direct production and checking pass with result SHA-256
04935cb96fa6631d2dfb0dbc3b3b053ad3efc7c966c3cb993edbae3aba955d9d;
the serialized report SHA-256 is
6e27101c016ce9adf10826a13c88dbd0e4a9b43c448b6a55ba15218a7078a869.
Strict Clippy passes for both crates, with four core relation tests and one
evidence replay test.

This is finite concrete evidence for eight declared memory cases, not a
universal loop theorem, solver certificate, arbitrary-address theorem, timing
claim, or minimality result for any of the three listings. The reader invariant
and local movement proofs remain the universal argument. The book object and
manifest still need to bind this report.
