# Lane: solver-decomp — the god-crate's worst cycle, halved

<!-- plan-section: lane-status -->

**Measured `axeyum-solver`'s module graph, then landed the first real slice of
refactor item [03](../../refactor-2026-08/03-solver-decomposition.md): the
largest dependency cycle drops from 65 modules to 24** (`WIP`, solver-decomp,
2026-08-15). Cut off by the account's monthly spend limit one step from done —
its last words were *"now update `model.rs` to import all five from the data
module, and fix the module doc"* — and landed by the coordinator in `25ab64649`.

**The finding.** Each quantifier certificate type was defined beside its
**checker**. So `Model`, the crate's base value type, depended on five quantifier
checker modules, and through two of them on the dispatcher, the `QF_BV` route,
the e-graph, the theory solvers, and back to `Model`.

| | largest cycle |
|---|---|
| before | **65 modules, 115,840 lines** — half the crate |
| after | **24 modules, 58,215 lines** (25.8%) |

Measured by this lane's own `scripts/analyze_solver_module_graph.py` (`3740597f5`,
which also pins `solver-module-graph-baseline.json`), and **re-run by the
coordinator before landing** rather than quoted from a commit message.

**The rule the new module enforces:** a value type may depend on the *shape* of a
certificate, never on the search or the checker that produces it.

**Gates on the assembled worktree:**

```
cargo test -p axeyum-solver --lib --features full          1155 passed, 0 failed
cargo clippy -p axeyum-solver -p axeyum-lean-kernel
  --all-targets --all-features -- -D warnings              exit 0
scripts/analyze_solver_module_graph.py                     exit 0
```

`model.rs` was already finished; the coordinator's only edit was the module doc —
one missing pair of backticks that failed `clippy -D warnings`, which is why the
lane's own last step was that doc.

**What is NOT claimed.** This is one slice, not the decomposition. **No crate was
extracted**, the 267-entry re-export façade is untouched, and ADR-0001's
"boundary proven by use" bar has not been argued for any new crate. The lane was
also briefed to re-measure `03-solver-decomposition.md` against the current tree
and report where that document has gone stale; it did not get that far.
