# Lane: agent-kernel-adversary — attacking the kernel with Lean's kernel

<!-- plan-section: lane-status -->

**Round 3: a fourth kernel-vs-Lean defect found and fixed, and the corpus
widened from 51 families to 66 over a development that finally carries the
constructs the kernel works hardest on (`DONE`, agent-kernel-adversary-2,
2026-08-18).** Rounds 1 and 2 damaged a `Prop`-only development, so 51 families
were rewiring the same handful of record shapes. Round 3 put a Type-valued
STRUCTURE (with a theorem provable only by structure eta), a `Nat` LITERAL (with
a theorem provable only by literal/constructor conversion), an INDEXED family, a
PARAMETERIZED recursive family, a MUTUAL group, an `axiom`, an `opaque` and the
`abbrev`/`opaque` reducibility hints on the wire, and added 15 families for
fields nothing had ever damaged: `levelParams` and `all` on families,
constructors and recursors; universe-parameter PERMUTATION at the binding site
and at the `Const` reference; a short universe-argument list; ι-rule right-hand
sides exchanged between rules of one recursor, and the rules permuted.

Detail moved to [`../notes/58-kernel-adversary.md`](../notes/58-kernel-adversary.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | (this change) | Round 3: corpus widened 51 -> 66 mutation families over a development that now carries a Type-valued structure, a `Nat` literal, an indexed family, a parameterized family and a mutual group; a fourth defect found and fixed — a **recursor's** `levelParams` was decorative, because a recursor is generated and compared rather than admitted, and the comparison's positional alpha-rename leaves an unbound parameter untouched |
| 2026-08-18 | `2633d7186` | Kernel-vs-Lean differential widened to 51 mutation families; recursor/constructor regeneration compared against Lean's own, closing the 37% of the stream `addDeclCore` never reads; two defects fixed — universe closure on `check_declaration` **and** the inductive gate, and the recursor `k` flag validated on import |
