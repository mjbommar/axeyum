# Lane: curriculum-graph-truth — the curriculum DAG did not know what the kernel had proved

<!-- plan-section: lane-status -->

**The graph's `status` field is the SCENARIO axis, and reading it as the kernel
axis inverts two of three destinations** (`COMPLETE`, curriculum-graph-truth,
2026-08-31). `mathtour.rs` defines `Status::Covered` as "has a self-checking
exercise family today" and a test enforces exactly that; `LeanHorizon` means
"primarily a proof-reconstruction target, not a benchmark". Measured over 2,562
axiom-free declarations, `calculus` is `lean-horizon` with **349** kernel
declarations — the largest node after `naturals`, carrying the FTC, MVT, Rolle,
IVT with an exact root, EVT, `supOn` and the Weierstrass M-test — while
`linear-algebra` is `covered` with 55 and is the thinnest destination.

So the repair is a second axis, not a status flip: flipping `calculus` to
`covered` would assert a scenario family that does not exist and break
`covered_nodes_have_a_family_realized_by_a_self_checking_scenario`. `kernel_decls`
is now measured per node by `scripts/measure-curriculum-kernel-coverage.py`,
whose `--expect-attributed` / `--require-node` guards each fail (exit 1) when
violated. Four summaries that were false rather than incomplete are repaired,
and `calculus.md` — missed by the 2026-08-30 sweep that fixed both siblings —
now carries a 24-row measured table. Decision and the full retrospective:
[ADR-1075](../../research/09-decisions/adr-1075-the-curriculum-graph-measures-scenarios-not-the-kernel.md).

**Two corrections for whoever reads this next.** `graph_dispatcher.py` does
**not** read `status` — it loads the field and never uses it, ranking
destinations by published infrastructure-frontier rows because ranking by
curriculum status "would be fabricating priority the data does not support". The
defect was documentation integrity, not dispatch. And `python3
scripts/gen-import-backlog.py --check` is **RED on `main`** and is not this
lane's: the fact ledger moved 147 → 164 qualifying rows without
`artifacts/import-backlog.json` being regenerated, confirmed independent (the
regenerated diff touches only fact rows). Deliberately left alone.

**Live work this measurement names.** Linear algebra's keystone is the
determinant at **general `n`** (cofactor recursion over the dimension bound; a
permutation sum needs data this kernel has no type for) — the matrix layer it
was previously blocked on has landed. Number theory's three live rungs are
factorization uniqueness restated as multiplicity agreement, Euler's theorem
`a^φ(n) ≡ 1 (mod n)`, and quadratic reciprocity. And **probability has 47
axiom-free `Rat` declarations through the weak law of large numbers with no
curriculum node at all**.

Rust `mathtour` tests were **not run** (cold worktree build) and are unaffected
by construction: no `status`, `family`, `prerequisites` or `unlocks` value
changed, and they read the Rust `NODES` mirror rather than the TOML. Checks that
did run: `validate-foundational-concepts.py` (137 rows), `validate-claims.py`
(104 claims, 0 errors), `gen-adr-index.py --check` (692 rows, no new
duplicates), `check-links.sh` (all links ok).

<!-- plan-section: landed-changes -->

| 2026-08-31 | `7c8adedb9` | ADR-1075: the curriculum graph measures scenarios, not the kernel. Records why the repair is a second axis rather than a status flip, that `lean-horizon` does **not** suppress dispatch (`graph_dispatcher.py` never reads `status`), three stale negatives found along the way (two of them this lane's — `--name-like matrix\|determinant\|eigen` returned a correct and useless ABSENT for a kernel that spells linear algebra `Rat.det2`/`det3`/`dotN`/`matMul`), and 47 axiom-free probability declarations the 23-node graph has no node for. |
| 2026-08-31 | `448368dea` | Spivak-shaped depth proposal: an eleven-rung spine for `number-theory` and a nine-rung one for `linear-algebra`, every "kernel has it" claim checked against `kernel_declaration_projection`. Not applied to `curriculum.toml` — ~30 new nodes moves five consumers plus the Rust mirror. Also corrects `linear-algebra.md`, whose "the matrix layer is unbuilt" was true on 2026-08-30 and false now (`Rat.matMul`, `matMul_assoc`, `matTranspose_mul`, `cramer2_*` all landed), moving the destination from a measured 25 to 55. |
| 2026-08-31 | `2594cd1e8` | `calculus.md`'s Lean-horizon paragraph named continuity, differentiability, the MVT, the FTC and series convergence as out of reach — every one is landed and axiom-free over `CReal`. Replaced with a 24-row measured table (every declaration name verified present) plus a "Still Lean-horizon" section naming what genuinely is: non-constructive limit reasoning, multivariable/metric calculus, measure theory, transcendence. |
| 2026-08-31 | `fba163147` | `curriculum.toml` gains a measured `kernel_decls` per node, the regeneration command in its header, and four repaired summaries (`calculus` said "ε–δ is Lean-horizon"; `sequences-and-limits` said "the ε–N definition is Lean-horizon" against a declared `CReal.Converges`/`Cauchy`/`limit`; `complex` said "analysis is Lean-horizon" without its 263 declarations; `cardinality` omitted `Nat.countRange`). No `status` or `family` value changed. |
| 2026-08-31 | `722ce2edd` | `scripts/measure-curriculum-kernel-coverage.py`: attributes the kernel's full declaration surface (all kinds — the theorem inventories cannot see `CReal.integral`) to the 23 curriculum nodes. Exit status depends on the finding: `--expect-attributed`, `--require-node` and an unknown node id each verified to exit 1. |
