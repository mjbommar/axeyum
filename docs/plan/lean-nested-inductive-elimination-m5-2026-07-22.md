# Lean nested-inductive elimination M5: computation and assurance

Date: 2026-07-22

Status: complete; M6 final bounded closure is next

Computation checkpoint: `edfa7924adde416393db74325bf29ce280e3f8a7`

Frozen plan:
[M5 computation and assurance plan](lean-nested-inductive-elimination-m5-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

## Result

M5 closes separate official-source and Axeyum-product computation evidence for
all three registered nested-inductive shapes. Each completed import now exposes
an exact theorem proof whose inferred type agrees, whose `Eq` sides are
definitionally equal, and whose recursively normalized left side reaches the
registered three-, three-, or five-successor constructor form.

The append-only `tl2_14_update` preserves every M0, Stage B, product, TL2.12,
and TL2.13 observation. The current seven-row construct matrix now has six
independently admitted rows, four computation-checked rows, and zero current
transactional declines. Only after that overlay validated did M5 remove the
obsolete live `inductive-nested` compatibility code. The five unrelated live
declines remain exact.

This is computation and current assurance credit, not final TL2.14 closure.
ADR-0355 remains proposed; M6 owns the final aggregate gates, decision
disposition, and complete project-state reconciliation.

## Pinned Lean reproduction

The unchanged M0 source compiled twice under pinned Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, one worker, and the registered
`MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=512M` systemd scope.

| Run | Exit | Wall | Maximum RSS KiB | OLEAN SHA-256 |
|---|---:|---:|---:|---|
| 1 | 0 | 1.50 s | 457,700 | `d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2` |
| 2 | 0 | 0.26 s | 462,308 | `d7d03cb863626f1ddc2a80b0dee3ae19fbc001dc2fb4ac60f6b9e27c7b7f53c2` |

Both 374,840-byte OLEAN outputs are byte-identical to the M0 digest. No source,
fixture, or retained export stream was regenerated or rewritten.

## Exact Axeyum computations

For each selected theorem, the M5 test:

1. retrieves the exact exported `Declaration::Theorem`;
2. infers its proof value and compares the inferred type with the theorem type;
3. requires an `Eq` head with exactly type, left, and right arguments;
4. checks the two sides by trusted definitional equality;
5. compares the right side with the registered normal form; and
6. recursively WHNF-normalizes application spines to force nested recursive
   calls beneath constructor heads.

| Registered ID | Exact theorem | Exact normal form |
|---|---|---|
| `auxiliary-recursion-computation` | `AxeyumNestedInductiveComputation.roseAuxiliaryRecursorComputes` | `MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))` |
| `indexed-container-computation` | `AxeyumNestedInductiveComputation.indexedAuxiliaryRecursorComputes` | `MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))` |
| `repeated-container-reuse-computation` | `AxeyumNestedInductiveComputation.repeatedContainerReusesAuxiliaryRecursor` | `MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ (MiniNat.succ MiniNat.zero))))` |

Each computation imports and reduces twice inside the focused test. The full
reports remain 122/8/494/17/34/0, 134/8/554/17/34/0, and
122/8/518/17/34/0, with zero axiom identities and one declaration identity per
admitted declaration. The construct row remains admission-only at
70/6/322/10/22/0.

The focused timed gate, including its incremental build, completed in 1.07 s
at 170,852 KiB maximum RSS. This is a bounded validation observation, not a
Lean-versus-Axeyum performance comparison.

## Append-only assurance

The current construct-matrix registration appends `tl2_14_update` after the
frozen TL2.12 and TL2.13 overlays. It binds:

- computation checkpoint `edfa7924adde416393db74325bf29ce280e3f8a7`;
- the exact product test and two-run resource policy;
- the two pinned-Lean measurements and one frozen OLEAN digest;
- the complete nested construct report; and
- the three immutable stream hashes, sizes, records, theorem names, normal
  forms, and complete reports.

The generated matrix reports exactly:

- seven rows, six official accepts, and one official-source rejection;
- six independently admitted rows;
- four `dual-admitted-computation-checked` rows;
- two `independently-admitted` rows;
- one `official-source-rejected` row; and
- zero current transactional declines.

The nested boundary names all three companion computations. Historical Stage B
blocker inventories remain frozen evidence and were not rewritten.

Historical hash projections remain exact after excluding only registered later
overlays:

- TL2.14 M0: `53ddf887ee068e4cf727bd22159f6195e7de743f3f2b4632694ed1797bfdec8f`;
- TL2.13 M0: `f6c11499ab38130de75c7acbd7ad1db79afcd080ab405a7233087f8f67c3ac3e`;
  and
- strict-positivity M3: the same `f6c11499...ac3e` historical boundary.

The live compatibility contract now has five registered unsupported codes and
no `inductive-nested` entry. M5 did not relocate the dead marker or introduce a
historical-document workaround.

## Validation

All Rust commands used one Cargo job and one test thread under the registered
4 GiB resource envelope and this worktree's own target directory.

- the focused nested suite passed six tests, including two reductions for each
  selected computation;
- the complete importer suite passed 47 integration tests;
- the complete kernel suite passed 188 unit tests and every integration target;
- exact 640 nested, 720 mutual, 768 recursive-IH, and 840 positivity
  populations remained green;
- the M2 23-case native matrix, M4 20-class importer boundary, recursor-order
  non-authority, and well-founded 35/0 control remained green;
- warning-denied importer Clippy and rustdoc passed;
- the importer compile-fail doctest and direct Rust formatting check passed;
- 73 related Python contract tests passed, including the new TL2.14 schema,
  order, report, resource, hash, normal-form, and reduction mutations;
- current construct-matrix and compatibility generators passed;
- M0 nested, TL2.12 recursive, TL2.13 mutual, and strict-positivity historical
  checkers passed without changing their frozen observations;
- parity documentation remained `DISAGREE=0`;
- foundational resources, documentation links, shell syntax, and
  `git diff --check` passed; and
- both computation and assurance diffs received independent read-only audits
  with no blockers.

## Scope and handoff

M5 establishes exact product computation and current assurance for the frozen
nested-inductive population. It does not claim native Lean nested syntax,
pattern or recursion elaboration, well-founded source lowering, broader
`Init`/`Std`/mathlib compatibility, proof tactics, runtime/compiler support,
full kernel parity, or ecosystem replacement.

M6 is next. It must run the final aggregate gates, accept/reject/defer ADR-0355
strictly from its registered exits, and reconcile PLAN, STATUS, project state,
roadmaps, P6.0, the research question, decisions index, generated documents,
and the final handoff. No final-completion claim is made here.
