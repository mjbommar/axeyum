# Lane: det-row-expansion

<!-- plan-section: lane-status -->

**Partially landed, and the remainder is sized.** Took law 3 of the four
ADR-1120 named over `Rat.det`: expansion along a *general* row, not only row 0.
Seven theorems landed — the whole index layer and the whole range layer — and
the summand identification did not. ADR-1135 said this law was "not blocked by
a missing type and not sized"; it is sized now, and the route turned out to be
**shorter than the classical one**.

The move that makes it cheap: a cofactor sum runs over a range ONE SHORT,
reindexed by `matSkip`, and the classical proof splits the resulting rectangle
at its diagonal into two triangles — which needs a triangular Fubini, which
needs `Nat.sub` in a summation bound and is not in this prelude. Instead,
**fill each inner sum back to the full range** (`Rat.sumRange_matSkip`), and
the double sum becomes a plain rectangle that `Rat.sumRange_swap` already
handles. Reasoning and the sizing of what remains: [ADR-1155](../../research/09-decisions/adr-1155-general-row-expansion-is-one-fubini-once-the-range-is-full.md).

The finding worth carrying beyond this lane: verified numerically, **the
double expansion along row `0`-then-`i-1` and the row-`i` expansion are
indexed by the same ordered pairs of distinct columns and agree TERMWISE, for
every `i` at once** (225 `(n, i, matrix)` cases). So general-row expansion is
ONE induction on the row index, not the row-1 case plus a ladder of adjacent
row swaps. Row antisymmetry — the expensive part of the classical route — is
not on the critical path.

## Landed changes

| what | where |
| --- | --- |
| `Rat.matSkip_zero`, `Rat.matSkip_succ_succ`, `Rat.matSkip_comm`, `Rat.matMinor_col_comm`, `Rat.det_minor_col_comm` — the index layer, all admitted first attempt, empty axiom footprint | `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` |
| `Rat.sumRange_peel_head`, `Rat.sumRange_matSkip` — the range layer, same | same file |
| `the_laplace_index_layer_hypotheses_are_load_bearing` — three paired `def_eq` controls, each negative on a ground instance where the premise fails and positive on one differing in a single index | `crates/axeyum-lean-kernel/src/rat_prelude/rat_prelude_tests.rs` |
| `F:rat-mat-skip-comm`, `F:rat-sum-range-mat-skip`, `F:rat-sum-range-peel-head`, `F:rat-det-minor-col-comm` | `artifacts/facts/` |
| ADR-1155 and its re-runnable numeric checks | `docs/research/09-decisions/` |

## Checks run

- `cargo test -p axeyum-lean-kernel --lib rat_prelude::` — **152 passed, 0
  failed** (389 s, with a sibling lane running the same sweep concurrently).
  The full prelude sweep, not a filtered subset: one bad declaration poisons
  the shared prelude build. Baseline before this lane was 151 tests; the extra
  one is this lane's control.
- The prelude BUILD alone (`rat_prelude_builds`) went 13.7 s → 31.8 s across
  this lane's seven declarations. Worth watching but not the runaway shape
  ADR-0584's family describes: the build is cached per process, so the sweep
  pays it once.
- `python3 scripts/validate-facts.py` — exit 0, 2,126 kernel-lean facts.
  `check-fact-depends-derived.py --fix` supplied three edges the proof terms
  carry (`Rat.add_assoc`, `Rat.add_comm`, `Rat.sumRange_peel_head`).
- `python3 scripts/check-settled-fact-statements.py` — PASS, 2,214 pinned, 0
  unpinned, 0 drifted. Every `formal.statement` was dumped from
  `Kernel::render_lean` FIRST and then pinned, because `--write` records
  whatever is already there.
- `python3 scripts/gen-adr-index.py --check` — 707 rows, no new duplicate
  numbers.
- `python3 docs/research/09-decisions/adr-1155-laplace-route-checks.py` — exit
  0. Verified to FAIL (exit 1) when the simulated `matSkip`'s branches are
  swapped.
- **Mutation, per declaration.** `declare_matrix_det`'s 24 steps were rewritten
  in an isolated snapshot to REPORT each rejection instead of short-circuiting,
  so one run gives a full table rather than only the first failure. Snapshot
  deleted; `git status` clean. Results, paired with whether the STATEMENT is
  still true under the mutated definition (checked separately by simulation,
  because three of the rejections are confounded by an upstream declaration the
  mutation had already removed):

  | declaration | rejected? | statement still true? | coverage added |
  | --- | --- | --- | --- |
  | `matSkip_zero` | yes | **no** | **yes** — cheapest discriminator in the file |
  | `matSkip_succ_succ` | yes | **yes** (64 of 64) | **none** — the proof's `bool_cases` motive names the branches in order, so the proof breaks while the theorem stays true |
  | `matSkip_comm` | yes, via the missing dependency | no (36 counterexamples, smallest `(0,0,0)`) | yes, on the statement |
  | `matMinor_col_comm` | yes, same confound | no (148 of 400) | yes, on the statement |
  | `det_minor_col_comm` | yes, same confound | no (125 of 400) | yes, on the statement |
  | `sumRange_peel_head` | **no — admitted** | yes, mentions no `matSkip` | none, by construction |
  | `sumRange_matSkip` | yes | no (228 of 300) | **yes** |

  `matSkip_succ_succ` is the row that matters: reasoning from semantics said it
  survives, running the mutation said it is rejected, and **only the pair is
  honest** — recording just the rejection would have claimed index coverage
  this theorem does not have. Also measured, extending ADR-1135: the whole
  `det matId n = 1` cluster (`det_congr`, `matMinor_matId`, `det_matId`) and
  `det_eval_singular` are all ADMITTED under the swap, while `det_eq_det2`,
  `matMinor_eval_example`, `det_eval_example` and `det_eval_example4` are
  rejected. `det_eq_det2` remains the discriminator, exactly as ADR-1135 said.

## Next

The summand identification, named exactly in ADR-1155's "What remains": a
`Nat.beq`-guarded `W` defined on the whole square, two index lemmas
(`unskip (matSkip j k) = k` and `Nat.beq j (matSkip j k) = false`), two
case-split proofs that the two parametrisations hit `W`, an `altSign` parity
step, and then `sumRange_matSkip` twice plus `Rat.sumRange_swap`. Bulk is in
the two identifications. Nothing in it needs a type this kernel lacks.
