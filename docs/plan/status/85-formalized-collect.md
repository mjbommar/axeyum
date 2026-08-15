# Lane: formalized-collect — importing the world's formalized mathematics

<!-- plan-section: lane-status -->

**The importer is not the bottleneck; our kernel's definitional equality is
(`WIP`, formalized-collect, 2026-08-15).** The
[`docs/formalized-math-2026-08/`](../../formalized-math-2026-08/README.md)
strand had zero landed work for as long as it existed. It is started, from a
measurement: 40 well-known Lean `Init`/`Std` theorems exported one at a time by
an official `lean4export` binary (commit `a3e35a58`, toolchain 4.30.0) and put
through `axeyum-lean-import` — **13 admitted, 27 declined, and every decline came
from `Kernel::add_declaration`, none from the reader**, at any size from 6 KB to
500 KB. The declines cluster into four causes, the largest being that `Nat.add`
is compiled through `Nat.brecOn`/`Nat.below`/`Nat.add.match_1` and does not
reduce for us — so **`Nat.add_comm`, the most cited theorem in our own fact
ledger, cannot be imported**. Landed with it: five facts on the new
`imported-kernel-lean` route (ADR-0454), each citing a SHA-256-pinned stream in
`artifacts/lean-imports/` and re-derived by two independent checkers (our kernel
and a real Lean 4.30.0 `#print axioms`); `01-collect.md` rewritten against
measured, cited figures with a table of nine things the first draft got wrong. A
sixth import was written and withdrawn: `Nat.not_succ_le_zero` is already proved
axiom-free in our own Nat prelude, so landing it as an import would have
understated what we hold — and the two are the same proposition under different
formal statements, which is the alignment problem arriving early.

Next, in priority order: (1) the **decline census** — export a few hundred `Init`
declarations, import each, report blocker clusters; a fail-closed importer at
13/40 reports only the first blocker in a stream, so this is the only way to size
the work, and it is minutes of compute; (2) hand the kernel lane the
**`brecOn`/`below` reduction** gap, which alone unblocks 15 of the 27 observed
declines; (3) re-pin the toolchain deliberately — `lean4export` HEAD tracks
`v4.34.0-rc1` while we are on 4.30.0, and moving re-exports every committed
stream and changes every pinned digest, so it is one decision made once.
**Not** blocked on a Mathlib clone: cloning before the census is collecting
ahead of the constraint.

<!-- plan-section: landed-changes -->

| 2026-08-15 | `33cbe5131` | Formalized-math strand started: real Lean import measured at 13/40 with a four-cluster blocker census, `imported-kernel-lean` proof route (ADR-0454), five imported facts with pinned streams, `01-collect.md` rewritten against cited measurements. |
