# Tock integer logarithms — bounded external verification case study

## Outcome

Axeyum authenticated and verified two public integer-logarithm helpers from the
exact owning build of Tock revision
[`ac5d597d22fbf3b03ef2169a577bac246ef65ffb`](https://github.com/tock/tock/commit/ac5d597d22fbf3b03ef2169a577bac246ef65ffb):

- `kernel::utilities::math::log_base_two(u32) -> u32`; and
- `kernel::utilities::math::log_base_two_u64(u64) -> u32`.

The accepted scoreboard contains **eight proved rows**, **six refuted and
replayed mutation controls**, **zero `UNKNOWN`**, and **zero `DISAGREE`**. No
Tock defect was found, so there is no upstream bug report. This result is a
concrete checked-proof use case over two production helpers; it is not a
whole-kernel, compiler-correctness, or performance-lead claim.

The machine-readable committed result is
[`proof-v4-result.json`](../../../bench-results/verify-tock-log2-20260721/proof-v4-result.json).
Its stable result identity is
`c4acae04f928a77d5ba2bb714c8d3269e42b0136e44bd384c6eeb229564aa37c`.

## What was authenticated

The target-selection and capture protocol bind all of the following before a
property query is admitted:

- the exact Tock commit and tree, source-file hash, owning Cargo manifests and
  lockfile, dual MIT/Apache license files, and pinned nightly toolchain;
- two independently materialized source trees at the same virtual path;
- two raw-identical 2,651,673-byte LLVM 22 modules, both with SHA-256
  `f9a1e1558d154b8238deae2f38f06ff251f6438ead8e109e4407b0e3998c76fd`;
- exact rediscovery, extraction, assembly, and checked admission of the two
  selected symbols; and
- explicit LLVM call-result `range` poison and `llvm.ctlz` zero-poison
  semantics rather than syntax stripping or source substitution.

Capture identity
`9ec0a0c3d0c4779b09b4b26ec56ea75153b0fab05a61b9b9b68a8bb709084b9d`
binds that chain. The detailed provenance and rejected shortcuts are recorded
in the [target-selection note](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md)
and [ADR-0334](../../research/09-decisions/adr-0334-preregister-tock-llvm-capture-v3.md).

This establishes reproducible ownership of the reflected LLVM functions. It
does not prove rustc or LLVM correct, nor does it prove a general equivalence
between Rust and LLVM semantics.

## What was proved

For each width, Axeyum proved four universal properties over the reflected LLVM
semantics:

| Target | Input domain | Proved properties |
|---|---:|---|
| `log_base_two` | all `2^32` inputs | definedness, the explicit zero result, equality with an independent floor-log specification, and the most-significant-set-bit characterization |
| `log_base_two_u64` | all `2^64` inputs | definedness, the explicit zero result, equality with an independent floor-log specification, and the most-significant-set-bit characterization |

The independent specification is a threshold partition over BV comparisons,
shifts, extracts, and `ite`; it does not call `ctlz`, `leading_zeros`,
`checked_ilog2`, or the reflected body. The 64-bit proof includes the compiler's
explicit narrowing to the `u32` return.

Three mutations per width exercise the teeth of the check: a wrong index
constant, an inverted zero arm, and a corrupted high partition. All six yield a
counterexample, replay the unmodified reflection, and agree with a native Rust
oracle. At the sign-bit witnesses, the native/reflected results are 31 for
`2^31` and 63 for `2^63`; every mutation differs.

## Evidence and trust chain

Each positive row uses the existing
`certify_qf_bv_unsat_end_to_end_within` route:

1. bit-blast the negated property with the production and independently
   implemented reference bit-blasters;
2. prove those bit-blastings equivalent with an unsatisfiable miter and recheck
   its DRAT artifact;
3. Tseitin-encode the admitted goal;
4. prove the final CNF unsatisfiable and recheck its DRAT artifact; and
5. recheck the final LRAT artifact when present.

Every accepted row reports certified bit-blast-miter, Tseitin, and SAT-
refutation trust steps. The committed summary records the size and SHA-256 of
every final DIMACS, DRAT, and LRAT artifact. The substantive 64-bit rows are:

| Property | Terms | Query time | DIMACS | DRAT | LRAT |
|---|---:|---:|---:|---:|---:|
| floor-log equality | 545 | 4.887294 s | 44,705 B | 13,286 B | 69,284 B |
| MSB characterization | 991 | 6.273062 s | 45,769 B | 6,081 B | 57,481 B |

The independent-reference faithfulness miter is common and simplifies to a
12-byte DIMACS plus 2-byte DRAT artifact. The final property refutations above
are the nontrivial proof objects. The independent bit-blaster is extensively
tested, including exhaustive small widths, but is not itself a theorem-proved
width-parametric implementation. This is therefore Axeyum's current checked
DRAT/LRAT trust standard, not a Lean-kernel end-to-end theorem.

The full generated certificate/result bytes remain ignored locally because
they derive from third-party build artifacts. The committed summary carries
their exact hashes and sizes, and its `local_result_sha256`
(`80e89d0eb2fc8fea7bdfd2a946542ae06b63b078e319cc62e283e831c9668d00`)
was compared field-for-field with the accepted local result. The producer is
regenerable from pushed source and pinned inputs; the compact repository record
is an authenticated index, not a vendored copy of every proof byte.

## Measured cost

The accepted fresh archived run reports:

| Measure | Result |
|---|---:|
| Property-query wall time | 12.699759 s |
| Authenticated runner wall time | 12.713594 s |
| Fresh Cargo wall time | 50.740 s |
| Outer wall time | 50.745 s |
| Peak RSS | 1,256,496 KiB (about 1.20 GiB) |
| OOM / group-kill / kill deltas | 0 / 0 / 0 |

These are artifact-production costs under the frozen protocol. They are not a
solver comparison and do not support a speed headline. Most of the fresh outer
time is compilation/protocol overhead; most query time is in the two 64-bit
universal properties.

## Comparison with the target's existing validation

At the pinned Tock checkout, the source itself is concise and explicit:
`checked_ilog2().unwrap_or(0)`. The ordinary Rust build type-checks and compiles
that implementation. An exact repository search finds no dedicated check that
names either helper outside its defining file. That observation does not imply
that Tock lacks project-level CI or higher-level testing; it only bounds what
was found for these two helper names at this revision.

| Dimension | Tock's source/build validation at the pinned revision | Added by this Axeyum case study |
|---|---|---|
| Inputs | executions selected by callers or tests | universal `u32` and `u64` input domains |
| Contract | source documentation and `checked_ilog2` implementation | four explicit properties per helper, including zero and definedness |
| Compiler artifact | owning build emits the functions | exact module/function provenance plus checked LLVM 22 `range`/`ctlz` semantics |
| Failure sensitivity | compiler and any existing test/CI failures | six replayed semantic mutations with concrete witnesses |
| Evidence | build/test outcome | independently rechecked dual-DRAT route plus final LRAT where present |
| Cost | normal project build/test workflow | target-specific capture protocol and a 50.745 s, 1.20 GiB fresh run |

The value is therefore assurance depth and reproducible evidence, not discovery
of a hidden target bug or replacement of Tock's normal testing. The selected
helpers were intentionally small enough to cross the external-build boundary
without first solving general memory, loops, or calls.

## Strategic interpretation

This result strengthens the reviewer-aligned **correctness and deployability**
spine in three concrete ways: it supplies a real external consumer, exercises
strict compiler-IR semantics that ordinary source-level checking does not
cover, and turns the DRAT path into a measured use case with independently
rechecked artifacts. It does not revive the retired performance-lead thesis.

The planning consequence is equally bounded: P5.5 v1 is complete, so the
roadmap should not widen Tock by inertia. Broader target work remains gated on
an independently selected need; active Track 5 effort can return to the named
P5.1 frontend and P5.4 fuzz-oracle residuals. The previously reviewed
concretization-policy sweep remains a reproducibility/configuration result, not
a reason to redirect this proof lane or start symbolic-memory work.

## Limits and follow-up

- Only two scalar helpers were selected. No pointer memory, loops, storage
  permissions, CRC path, scheduler, or whole Tock kernel is verified.
- The owning-build provenance binds the compiler output to the exact build; it
  does not verify the compiler transformation from Rust semantics.
- Native Rust replay is used for the six controls, not as a universal proof
  oracle for every input.
- The measured result establishes proof production and checking, not a
  performance advantage over Z3, Bitwuzla, Tock's tests, or another verifier.
- No target bug was reproduced, so responsible upstream reporting is not
  applicable. The useful upstream-facing artifact is this reproducible bounded
  assurance result, not an issue report.

This closes [P5.5](../../plan/track-5-verified-systems/P5.5-external-target.md)
under its measured external-target exit criterion. Any wider Tock claim needs a
new, separately preregistered target slice and must preserve the same exact
provenance, replay, trust, and resource-accounting discipline.

## Reproduction and records

- [Accepted compact result](../../../bench-results/verify-tock-log2-20260721/proof-v4-result.json)
- [P5.5 target selection and capture history](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md)
- [P5.5 task and exit criteria](../../plan/track-5-verified-systems/P5.5-external-target.md)
- [ADR-0338 accepted proof result](../../research/09-decisions/adr-0338-preregister-tock-proof-v4-marker-parser.md)
