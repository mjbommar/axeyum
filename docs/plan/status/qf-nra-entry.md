# Lane: qf-nra-entry — put QF_NRA on the parity board

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, qf-nra-entry, 2026-09-07).** Task:
`docs/plan/families/smt-quantifier-free/qf-nra.md` said QF_NRA was rank 1 of
the cheap parity targets — same input format, same protocol,
`scripts/parity-run.sh` needed no changes. Entering was a measurement task: a
committed 200-file list, a pinned reference build, one ledger entry with zero
disagreements, and a census of the losses. All four are done.

**Benchmark list**: `bench-results/parity-lists/QF_NRA.txt`, 200 files, sha256
`d645dd907edd60f62e4bbd815c2f420d3feaa88731e55ab4f63a7677705ef931`. Recipe
matches QF_LRA/QF_NIA/QF_UF/QF_BV (commits `aaa2d7541`, `025f4ba9f`,
`565284cf7`): `LC_ALL=C find <div> -name '*.smt2' | LC_ALL=C sort | awk
'NR%stride==1' | head -200`, population 12,154, stride 60. Committed before
any sweep.

**Reference**: `scripts/parity-run.sh` routes `QF_NRA` to
`/nas3/data/axeyum/harness/bin/cvc5` (same arm as QF_LIA/QF_NIA/QF_IDL/QF_RDL
— the fallthrough would be unpinned `/usr/bin/z3` 4.13.3, which did not
compete in SMT-COMP 2025). Plain invocation, no portfolio flags. Version
pinned in the ledger row: `cvc5 1.3.4 [git f3b21c4 on branch HEAD]`.

**Sweep**: built `smtcomp_cli` via `scripts/cargo-serialized.sh` and ran on
s5 (idle, `taskset -c 0-7`, 24s/8GiB) at solver commit `00373a7d42` (fetched
via `git fetch ssh://s4/…` into a reused detached worktree,
`/home/mjbommar/axeyum-parity-s1`, since `/home` is not shared across hosts).
Ledger row appended to `bench-results/PARITY.md`:

  axeyum 110/200, reference (cvc5) 186/200, ratio 59.1%
  both/axeyum-only/reference-only: 109/1/77, disagreements: 0 (SOUND)

Load 4.39 on 8 cores at sweep start (just after the release build) triggered
the script's load warning; `axeyum solved` is a floor under that, the ratio
is not (per the script header's own caveat) — recorded in the ledger row, not
hidden.

**Census** of the 77 reference-only losses: population from the scored
sweep's own sidecar (`axeyum=unsolved`, `reference` in `{sat,unsat}` —
**front door**, i.e. `smtcomp_cli`/`solve_smtlib`). Cause class per file comes
from `explain_corpus --list <one-file> 24000 --json --timed-trace` (one
invocation per file, each wrapped in an external `timeout -k 5 45`, per the
brief's fixed rule — none hung, though one hit the 45s kill and 4 others
errored before producing a trace): the class is the route with the **largest
`elapsed_ns`** among non-`probe` attempts, i.e. the route that spent the
budget, never the last route's message. Data: `bench-results/parity-losses-
20260906/QF_NRA.census.tsv` + `README.md` (method stated explicitly there,
including why it does not share the 2026-09-05 S3 census's refuted
last-route-message method, `b57800c06`/`f3ce8ef58`).

Result: 62/77 (80.5%) `nra-cross-product-admission-bound`, 7/77 (9.1%)
`nra-refinement-incomplete` — together 69/77 (89.6%), the generic
multi-variable nonlinear-abstraction route's documented sound-incomplete
boundary. 5/77 (6.5%) `diagnostic-instrument-inconclusive` (the trace
instrument itself failed on these five; front-door loss still holds, cause
does not). 3 singletons: `cas-ideal-refuter-incomplete`,
`nra-real-root-not-applicable`, `wide-int-admission-incomplete` (the last is
ADR-1702 slice 2, an already-tracked separate gap).

`docs/plan/families/smt-quantifier-free/qf-nra.md` updated from "not
entered" to the full ledger row + Cause section.

**Known pre-existing issue, not touched (out of scope for this lane)**:
`scripts/check-parity-docs.py` reports `docs/PROJECT-STATE.md` stale against
`bench-results/PARITY.md` for QF_IDL/QF_LRA/QF_RDL and the division count
("eleven" vs the ledger's now-thirteen), predating this lane's first commit
— confirmed by checking `docs/PROJECT-STATE.md`'s current numbers against
those divisions' PARITY.md rows before this lane touched anything. Not fixed
here; it is a global doc outside this brief's scope.

<!-- plan-section: landed-changes -->

| 2026-09-07 | qf-nra-entry | committed `bench-results/parity-lists/QF_NRA.txt` (200 files, sha256 `d645dd907edd`) |
| 2026-09-07 | qf-nra-entry | QF_NRA parity ledger row appended: 110/200 vs cvc5 186/200, ratio 59.1%, 0 disagreements (SOUND) |
| 2026-09-07 | qf-nra-entry | loss census committed (`bench-results/parity-losses-20260906/`), `docs/plan/families/smt-quantifier-free/qf-nra.md` updated from "not entered" to on the board |
