# 289 — the 96 MB Lean module for `14x + 21y = 5`

<!-- plan-section: lane-status -->

Lane: `diophantine-blowup`.

**Status: fixed, with a measured residual.** The immediate defect is a one-word
call-site bug and is landed. The Diophantine route's module size is still
superlinear in the coefficients, which is a separate, bounded piece of work
written up below rather than papered over.

---

## Step 0 — reproduced standalone, before reading any code

    target/release/examples/lean_hypothesis_binding_dump \
      artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2

    2.24 s wall, stdout = 96,297,506 bytes (91.8 MiB)
    stderr: BINDING_DUMP|...|fragment=Diophantine|assertions=1|indices=0

Independently confirms the finding lane's number.

## Where the size came from — measured, not suspected

The module is 234 lines. **One of them is 96,155,365 bytes — 99.85 % of the
file**: line 232, the body of `theorem axeyum_refutation : False :=`. The
next-largest line is 14,183 bytes. Not a diffuse blowup; a single proof term.

Hash-consing that one line back into a DAG (`scratchpad/dio-profile.py`, an
explicit-stack tokeniser over the 10.9 M-token line) gives the answer:

| | |
| --- | --- |
| distinct nodes in the term | **18,018** — 46 leaf, 17,972 application |
| printed as a tree | **96,155,363 bytes** |
| printed with full sharing (computed from the DAG) | **~967,245 bytes**, 99× smaller |
| most-repeated single distinct subterm | **169,184** occurrences |
| distinct app nodes occurring >10³ times | 291 |

Printed-byte attribution over that line, by occurrence count × own length:

    43,480,584  leaf `axeyum.reconstruct.dio.x._1`
    20,578,860  leaf `axeyum.reconstruct.dio.x._0`
    17,093,174  leaf `Int.add`
     9,767,528  `Int.add` application syntax
     1,705,104  leaf `Int.zero`

So **the dominant term is not any part of the argument — it is the tree
expansion of a small DAG.** The proof is a chain of `Eq.rec` rewrites
(30,527 occurrences, over `Int.add_assoc`/`add_comm`/`add_zero`), and a Lean
`Eq.rec` reprints its subject term about four times per step (the type index,
the motive body, the two endpoints). Nest hundreds of those and you get 4^depth
without a single large number anywhere.

### Root cause: the renderer was called at the wrong entry point

`crates/axeyum-lean-kernel/src/lean_pp.rs:885` builds a share plan **only under
`compact`**:

    let shares = if compact {
        self.compact_share_plan(&[goal, proof], theorem_name, &at_consts)
    } else {
        LeanSharePlan::default()
    };

and `reconstruct_diophantine_to_lean_module` called `render_lean_module` — the
non-compact one. So no sharing was attempted at all.

Detail moved to [`../notes/289-diophantine-blowup.md`](../notes/289-diophantine-blowup.md).

