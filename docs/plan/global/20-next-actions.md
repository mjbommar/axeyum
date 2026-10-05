## Next Actions

**P0 preempts every track:** a wrong verdict, a crash, data loss, or a gate that
cannot fail (or is red) is reproduced, root-caused, regressed and repaired
first. Otherwise work runs in five tracks; within a track, take the first
unblocked item. Tracks may run in parallel, one lane per item.

<!-- plan-generated: lane-status -->

### SOL — Solver parity

Close the measured gap to the named reference division by division, never
trading a verdict for speed. Every lever ships only under the ship criterion
(0 stable losses, 0 flips, ≥ 1 stable gain on pinned **and** held-out); a lever
that fails it stays OFF with its A/B in an ADR. Detail:
[families](docs/plan/families/README.md),
[stock-take 2026-09-16](docs/plan/five-divisions-stock-take-2026-09-16.md),
[CDCL consolidation plan](docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md).

1. **SOL-1 Re-measure the board on head.** The ledger frame `c1d6db6fe` is 976
   commits behind `a38d5f5da`; the A13 frame `db31113fa` is 425 behind; and the
   ledger is badly stale for QF_NIA (41 ledger vs 87 on the 09-17 board) and
   QF_DT (114 vs 171). Run all 16 lists through `scripts/parity-run.sh` at one
   commit, plus a same-day z3/cvc5 reference board on the identical lists.
   *Exit:* 16 ledger entries at one solver commit, 0 disagreements, and
   `scripts/check-parity-freshness.py` exits 0 (it exits 2 today — ENG-1).
2. **SOL-2 Finish CDCL(T) consolidation (phase B4).** ADR-1908 made the native
   core the one CDCL(T) driver, but `ufbv_online.rs:1468` and `:3498` still
   build `CdclT`; ADR-1913 scopes it as a swap gated on one probe. *Exit:* no shipping path
   constructs `CdclT`; board verdict-invariant against SOL-1.
3. **SOL-3 Linear arithmetic depth** (QF_LRA 107/145, QF_UFLRA 142/198,
   QF_IDL 113/123 on the ledger). In order: budget hand-back from a
   non-converging online search (the `ecoliMILP` shape) and the `sc-19…25`
   search cost; the 7 files stopped at a pivot-0 deadline poll
   (`simplex.rs:1441`); the 49 `cilled`/`minepump` QF_UFLRA files that land at
   ~25 s; `dl-online` as a portfolio arm and QF_IDL's 19 early declines.
   *Exit per lever:* ship criterion, plus the five LRA/DL/LIA z3 fuzzes green.
4. **SOL-4 Nonlinear and quantified** (QF_NIA, QF_NRA, UF/UFNIA/UFLIA).
   67 of 116 undecided QF_NIA rows timed out inside the linear relaxation
   (stock-take, before ADR-2148 shipped); S12's
   coefficient-width rung was never built; ADR-2149 (nested-binder activation)
   is registered OFF with no A/B run; ADR-2134 (+4 pinned QF_NRA, 0 held-out
   movers) stays OFF. *Exit:* one shipped lever per division under the ship
   criterion, or an ADR recording why the named mechanism is not the block.
5. **SOL-5 Dispatch cost and cause coverage.** `int-real-relax` decides 0 of
   198 rows while costing 754 s (ADR-2106); QF_RDL's last 2 files have no
   census; the families tree has no files for QF_DT, QF_S, QF_UFLRA and calls
   QF_FP "not entered". *Exit:* the rung is budgeted or removed by A/B; every
   ledger division has a family file with a cause or an explicit "no".

### LIB — Library and the flywheel

Make the flywheel automatic: the system should establish theorems nobody wrote
proofs for, through the one trust anchor (ADR-0601), as graded statement
families (ADR-0603). The metric is the trusted base and unassisted results, not
volume. The L0–L4 programme (ADR-0717) is done through S6, C3, G5 and D5;
what remains is below. Detail:
[throughput](docs/formalized-math-2026-08/05-throughput.md),
[CAS](docs/math-department/13-computer-algebra.md).

1. **LIB-1 Closed-loop batch discovery (D6).** *Exit:* a batch establishes a
   theorem whose checked proof consumes a theorem an earlier batch established,
   with no human-written target proof and an empty axiom footprint.
2. **LIB-2 Statement families, MOS-0.** None of the MOS files exist yet
   (`artifacts/statement-families/`, `scripts/check-statement-families.py`).
   *Exit:* every family row resolves to its declaration and receipt, and the
   targeted negative controls fail.
3. **LIB-3 CAS remainders.** Seven items of `13-computer-algebra.md` are `[~]`
   (1, 3–7, 9), e.g. moving four of five CAS arithmetic copies onto
   `axeyum-arith`, Galois groups, multivariate factorization. *Exit:* each item's
   own remainder, and the certified floor in `check-cas-trust-registry.py`
   rises above 151.
4. **LIB-4 Library artifact compatibility C4/C5.** C4's first demand-gated
   feature measured +0 population survival (ADR-1667). *Exit:* a C4 feature with
   nonzero survival, or C4 closed by ADR; C5 stays conditional on adapter use.

### EVD — Evidence and Lean

Every unsat/valid carries a machine-checkable proof, and every claim names
which check it passed. Detail: [evidence family](docs/plan/families/evidence/README.md),
[Lean](docs/math-department/14-lean-lang.md),
[proof-gap matrix](docs/plan/generated/proof-gap-matrix.md).

1. **EVD-1 Re-measure QF_BV evidence on head** (last: 93/130 certified,
   2026-08-17) and split the bare-UNSAT rows by route provenance; re-check
   whether the two QF_NIA `IntPow2` proof-production errors recorded in August
   still reproduce. *Exit:* a fresh evidence-mode ledger entry; zero production
   errors; certified, text-rechecked, arena-checked and bare counts kept apart.
2. **EVD-2 Delete the SOS reconstruction fallback.** ADR-1673 relabelled it and left
   deletion open; `reconstruct_sos_certificate_wrapper_to_lean_module` is still
   in `axeyum-solver/src/reconstruct.rs`.
   *Exit:* the wrapper is gone and no reconstruction emits a statement-only shim.
3. **EVD-3 Lean residuals.** ℤ and an LRAT route for `by axeyum` (ADR-1666 is
   ℕ only); the 50 `Type`-valued theorems and 34 blocked declarations
   (ADR-1661); the unfinished 1,077-command audit (107 excluded). *Exit:*
   each closes with its own run and regenerated Lean matrices
   (`gen-lean-compatibility.py --check`, `gen-lean-complete-parity.py --check`).
4. **EVD-4 Propositional SAT entry.** RAT in the backward elaborator, the last
   piece after ADR-1722. *Exit:* RAT proofs elaborate to LRAT checked by
   `check_lrat`.

### CON — Consumers

Real users drive the product surface: the Python bindings, cindergraph (C
source graphs) and Glaurung (binary analysis) consume Axeyum; the SMT-LIB front
door serves everyone else. Foreign repositories are pushed only by the user.

1. **CON-1 Glaurung's default-backend decision.** Its ADR-0272 timing
   campaign was inconclusive; re-register it with a work-bounded budget.
   *Exit:* a registered campaign result that decides the default.
2. **CON-2 The defects pipeline over a real C library** (cindergraph → QF_BV
   → `axeyum_cli` → sanitizer replay; `python/examples/cindergraph_defects/`).
   *Exit:* findings on an unmodified upstream library, each replayed.
3. **CON-3 cindergraph's `for (;;)` empty-body policy.** Needs a Joern run.
   *Exit:* the policy pinned by a test against recorded Joern output.
4. **CON-4 SMT-LIB session semantics.** ADR-0342 is still `proposed`:
   scoped declarations under `push`/`pop`, reset epochs, atomic continued
   errors; then `define-fun-rec`, full `(reset)`, parametric `declare-sort`.
   *Exit:* accepted ADR; textual fixtures compare ordered outputs; a malformed
   command cannot partially mutate session state.

### ENG — Engineering hygiene

Gates that cannot fail, stale labels and abandoned state are how false claims
ship. Detail: [architecture review](docs/research/11-design-review/2026-08-27-architecture-review.md),
[gate divergence](docs/refactor-2026-08/gate-divergence-2026-08-14.md).

1. **ENG-1 Red gates.** On `a38d5f5da`, 25 `check.sh` steps fail when run
   alone, including `check-parity-freshness.py` (exit 2: the `PARITY.md:1972`
   "Budget curve" header), `shape-duplicates`, `proposition-duplication`,
   `merge-hygiene`, `carcara-gate` and `kernel-stack-envelope`; 79 more failed
   only in a parallel sweep and are unconfirmed. The consolidation fixed three
   (`plan-authority`, `example-inventory-count`, its controls). List and method:
   [gate sweep 2026-10-05](../gate-sweep-2026-10-05.md). *Exit:* every step
   exits 0 alone on main (or is removed by an ADR), the unconfirmed 79 are
   classified, and each repaired guard has a control that kills exactly one test.
2. **ENG-2 Worktrees and branches.** `git worktree list` showed 201 entries on
   2026-10-05 before this consolidation (198 under `.claude/worktrees/`); 14 branches are unmerged into `main` (13 dated
   2026-08-22…31, one 2026-09-01). *Exit:* a read-only inventory classifies
   each (dirty/merged/unmerged/target size); unmerged work is merged or
   recorded abandoned; then exact-target removal.
3. **ENG-3 ADR status sweep.** 81 of 1,003 ADRs read `proposed` (counted 2026-10-05 from each file's first status line), including
   shipped decisions (ADR-2121, ADR-2126, ADR-2142). *Exit:* every decision on
   `main` reads `accepted`; every OFF lever reads `proposed` or `deferred` with
   its A/B.
4. **ENG-4 Split `creal.rs`.** It fuses name registry, field struct, build
   order and dispatch (441 fields at the review; 11,595 lines on 2026-10-05, after a partial split — topological order and the generated `STEPS` table landed, ADR-1512/1530). *Exit:* the review's split
   lands with prelude projection byte-identical and the kernel suites green.
