# Lane: curriculum-graph-truth

Status: IN PROGRESS (first commit, work incomplete)

Task: measure `docs/curriculum/curriculum.toml` against what the kernel
actually declares, correct the stale nodes, and propose a deeper Spivak-style
node decomposition for the `linear-algebra` and `number-theory` destinations.

First measurement (prebuilt `prelude_theorem_inventory --include-constructed`,
binary dated 09:31 against a last kernel-source commit of 09:26, so fresh):
2,118 distinct theorems, all axiom-free, across 10 preludes.
