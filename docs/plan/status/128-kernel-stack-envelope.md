# Lane: kernel-envelope — the kernel's stack was never measured, and `creal` had zero margin

<!-- plan-section: lane-status -->

**The kernel's stack requirement is now a measured, pinned, gated number, and
the numbers say the margin was zero** (`WIP`, kernel-envelope, 2026-08-26).

The trigger was `CReal.e` making
`every_creal_declaration_is_checked_and_axiom_free` — the single test behind
this project's axiom-freedom claim — SIGABRT instead of run. Exit 134 is
indistinguishable from a broken tool or an absent declaration, and this
repository has read it as both.

Bisected the real requirement (`scripts/check-kernel-stack-envelope.sh
--measure`): the smallest power-of-two thread stack on which each prelude
build completes.

| prelude | debug | release | ratio |
|---|---:|---:|---:|
| `cpoint` | **33,554,432** | 1,048,576 | 32× |
| `complex` | 4,194,304 | 262,144 | 16× |
| `creal` | **2,097,152** | 131,072 | 16× |
| `rat` | 1,048,576 | 131,072 | 8× |

`creal` in debug needs **exactly** the 2 MiB default a spawned thread gets,
which is what a `#[test]` runs on — there was never any margin, and one deep
declaration was always going to end it. `cpoint` needs 32 MiB, so the five
sites using a 64 MiB `on_a_deep_stack` copy had **2×** headroom, not the
comfortable margin the number looks like.

**The recursion-depth limit that was proposed is the wrong instrument, and the
measurements are why** (ADR-0584). Debug frames cost up to 32× release frames
at *identical* depth, so one constant cannot serve both profiles; the two deep
recursions cost ~2,250 B and ~576 B per frame, so depth does not predict stack;
and only `infer_core`/`check_core` return `Result` — `whnf_core`,
`def_eq_core_uncached`, `instantiate_aux` and `abstract_aux` cannot report one.
Lean 4.30's own kernel uses a **stack-pointer probe** with a 128 KiB margin
throwing a catchable `stack_space_exception`; the depth counter arrived only in
4.34, as a supplement. That design is deferred with its open questions written
down, not rejected.

Detail moved to [`../notes/128-kernel-stack-envelope.md`](../notes/128-kernel-stack-envelope.md).

<!-- plan-section: landed-changes -->

| 2026-08-26 | `bdfe77340` | One `DEEP_STACK_BYTES` (256 MiB) and one `on_a_deep_stack` replace seven verbatim copies at three unexplained sizes. `examples/kernel_stack_envelope` builds one prelude on an exact stack and answers with its exit status (0/134/2), refusing to run with the prelude cache on because a cache hit type-checks nothing and would report a requirement of ~0. `scripts/check-kernel-stack-envelope.sh` pins the table and halves every budget until the probe FAILS, so a green run has demonstrated it can go red. Six controls; each of the five guards mutation-verified to kill exactly one. |
