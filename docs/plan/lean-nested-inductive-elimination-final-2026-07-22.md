# Lean nested-inductive elimination: M6 final result and handoff

Status: ADR-0355 acceptance and TL2.14 DONE effective upon containing-commit publication

Date: 2026-07-22

Decision:
[ADR-0355, acceptance effective upon containing-commit publication](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Prior checkpoints:

- [M0 source/wire freeze](lean-nested-inductive-elimination-m0-2026-07-22.md);
- [M1 typed diagnostic preflight](lean-nested-inductive-elimination-m1-2026-07-22.md);
- [M2 native expansion and restoration](lean-nested-inductive-elimination-m2-2026-07-22.md);
- [M3 deterministic nested grammar](lean-nested-inductive-elimination-m3-2026-07-22.md);
- [M4 exact official import](lean-nested-inductive-elimination-m4-2026-07-22.md); and
- [M5 computation and assurance](lean-nested-inductive-elimination-m5-2026-07-22.md).

## Final result

Axeyum now implements the bounded pinned-Lean 4.30 nested-inductive admission
rule as a deterministic trusted-kernel prepass. It discovers structurally
nested container parameters without trusting exporter metadata, copies complete
container groups to fresh private auxiliaries, reaches a fixed point, invokes
the unchanged TL2.11--TL2.13 atomic group checker once, and restores only the
source surface plus deterministic `.rec_N` auxiliary eliminators. Every
published type and closed rule infers before the transaction commits; failures
publish neither partial declarations nor a `CompletedImport`.

The official construct and all three explicit computation streams import twice
with exact generated/exported comparison. Their registered theorem proofs
infer, have definitionally equal `Eq` sides, and normalize twice to the exact
three-, three-, and five-successor forms. The append-only TL2.14 assurance
overlay preserves every earlier observation and records seven rows, six
independently admitted rows, four independently computation-checked rows, and
zero current declines. The obsolete live `inductive-nested` code is gone; the
five unrelated compatibility codes remain exact.

## Accepted evidence

Exit gates 1--11 and every non-publication component of exit 12 are met. The
last operational condition is publication of the containing commit with local,
tracking, and remote ref equality:

1. P0 and M0 committed the exact Lean revision and source functions, baseline,
   sources, streams, hashes, cases, mutations, resources, and stop conditions
   before the first semantic change.
2. M1 first moved the valid nested row from accidental `Malformed` handling to
   exact typed `Unsupported(inductive-nested)` without admission.
3. Native discovery checks an existing inductive head, complete parameter
   prefix, group-family occurrence, and no loose bound variables. It does not
   trust `numNested`.
4. Expansion copies every family and constructor in a container group, permits
   differing outer/container parameter counts, structurally deduplicates
   repeated applications, and processes copied constructors to a fixed point.
5. The expanded group passes the unchanged complete-group positivity,
   motive/minor, target-family recursion, inference, and atomic rollback path.
6. Restoration removes private family and constructor references from every
   published type and rule while retaining deterministic `.rec_N` eliminators.
7. Native and importer tests reject invalid parameters, polarity, arity,
   indices, auxiliary order/name, restored declarations/rules, metadata, and
   late publication transactionally.
8. The 640-case public grammar repeats byte-identically at descriptor
   `a20fe056c9443a37`, with 320 admitted and 320 exact typed-reject profiles
   spanning all registered dimensions.
9. The construct and three computation streams import twice with exact
   generated/exported comparison. Pinned Lean and Axeyum reproduce all three
   registered normal forms twice.
10. The exact 720 mutual, 768 recursive-IH, and 840 positivity grammars,
    singleton/direct identities, well-founded 35/0 import, and completion-only
    publication controls remain green.
11. The append-only current matrix records nested admission and computation
    without changing ADR-0351, Stage B, product, TL2.12, or TL2.13 history.
12. Every bounded code, positive/negative pinned-Lean, contract, generated-
    document, parity, foundational-resource, link, and staged-path gate passes
    under the registered one-worker/4 GiB policy. This exit becomes complete
    when the containing commit is pushed with local/tracking/remote equality.

## Final bounded gates

`just` is not installed in this worktree environment, so M6 ran the documented
bounded underlying commands rather than treating `scripts/check.sh` as a
substitute for the lane-specific contract. Rust commands used one build job and
one test thread under `MemoryHigh=3G`, `MemoryMax=4G`, and
`MemorySwapMax=512M`.

| Gate | Result |
|---|---|
| kernel all-target/all-feature tests | 188 unit + 85 integration passed |
| importer all-target/all-feature tests | 47 integration passed |
| explicit doctests | kernel doctest and importer compile-fail doctest passed |
| generated populations | exact 640 nested + 720 mutual + 768 recursive-IH + 840 positivity passed |
| pinned Lean positive | two 374,840-byte OLEANs at frozen SHA-256 `d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2` |
| pinned Lean negative | both runs exited 1 at line 8 with the exact registered no-local-variable diagnostic |
| final Lean resources | positive runs: 1.23 s / 458,720 KiB and 0.23 s / 463,324 KiB; negative runs: 0.49 s / 445,612 KiB and 0.13 s / 445,544 KiB |
| focused Rust formatting | all TL2.14-owned Rust files passed direct `rustfmt --check` |
| warning-denied Clippy | kernel/importer, all targets and features, passed |
| warning-denied rustdoc | kernel/importer, all features, passed |
| Lean contract/parity suite | 73 related Python tests plus all registered generators/checkers passed; `DISAGREE=0` |
| construct assurance | 7 rows / 6 admitted / 4 computation-checked / 0 current declines |
| foundational resources | 137 concept rows and 174 packs validated |
| documentation and shell | links, shell syntax, and `git diff --check` passed |

The final topic-branch change must be pathspec-staged and independently audited.
Its publication gate requires the containing commit to be pushed and local/
tracking/remote refs to be equal before this result is handed off.

## Scope and non-claims

TL2.14 establishes a bounded nested-inductive kernel/import profile. It does
not establish:

- native Lean source parsing or inductive-command elaboration;
- pattern/equation compilation or structural recursion elaboration;
- well-founded/partial recursion elaboration or termination proving;
- every unsafe or universe/elimination profile;
- broad `Init`, `Std`, or mathlib admission;
- tactics, metavariables, typeclasses, modules, Lake, LSP, compiler/runtime,
  metaprogram, or `.olean` compatibility; or
- full Lean-kernel parity, consistency, or replacement of official Lean.

## Handoff

TL2.14 is complete and no semantic work remains in this lane. The broader Lean
program still owns TL2.8--TL2.10, TL2.15--TL2.16, prelude-assumption discharge,
native source/elaboration work in TL4, and ecosystem/runtime layers. In
particular, TL4.9/TL4.10 continue to own native inductive syntax, pattern and
equation compilation, structural/mutual/nested/well-founded source recursion,
and termination evidence. The already checked well-founded 35-declaration core
stream remains evidence about an elaborated result, not frontend credit.
