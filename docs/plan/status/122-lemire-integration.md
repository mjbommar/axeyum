# Lane: lemire-integration — a leaf module's size is not evidence that it is load-bearing

<!-- plan-section: lane-status -->

**The GF(2) machinery is on `main`; the Kaser--Lemire attack is not** (`landed`,
lemire-integration, 2026-08-23, ADR-0544, `b99d715bc`). Two lanes had produced
~1.3 M lines across four artifacts, and neither was mergeable whole: `main` was
57 commits ahead and **694 behind** origin, and `agent/gf2/lemire-proof` carried
the entire attack alongside the machinery.

Three things this cost, worth carrying forward:

**Sixty ADR numbers were double-allocated and `git merge-tree` reported no
conflict on any of them.** The branch allocated `adr-0484`--`0592` while
`origin/main` independently allocated `0484`--`0543`; the *filenames* differ, so
both sets merge clean and land side by side under one numbering. The generated
index would then render two different decisions as one sequence. A clean
`merge-tree` is evidence about content, not about a shared namespace — and this
repository has two such namespaces (ADR numbers, fact ids) that no merge check
covers.

**A module's size is not evidence that it is load-bearing.** `gf2_hayes.rs` is
26,655 lines and 266 public items, the largest module in `axeyum-cas`, and it is
a leaf: it imports nothing from the rest of the crate, and the only inbound
references from the keep-set were six in `gf2_extension.rs`, every one a doc
comment or `#[cfg(test)]`. The extraction that looked infeasible was four test
assertions.

**Grepping the module path missed a coupling that only failed at link time.**
`tests/gf2_artifact_cli.rs` reports clean for `gf2_hayes` and still reaches it,
through `env!("CARGO_BIN_EXE_axeyum-gf2-hayes-conditional-variance")`. When
cutting a module out of a crate the coverage surface is module paths **and**
`CARGO_BIN_EXE_*` names **and** `Cargo.toml` target declarations; a clean grep
over the first says nothing about the other two.

Which facts stayed was decided mechanically rather than editorially: a fact stays
iff every `evidence.artifact` it cites resolves under a retained path and no
checker command reaches `gf2_hayes` or `artifacts/gf2`. Exactly four of 45
qualify, `depends_on`-closed. The other 41 would have left the ledger asserting
evidence this repository can no longer produce.

Detail moved to [`../notes/122-lemire-integration.md`](../notes/122-lemire-integration.md).

