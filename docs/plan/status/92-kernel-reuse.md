# Lane: kernel-reuse — stop rebuilding the trusted prelude from scratch

<!-- plan-section: lane-status -->

**Landed process-wide prelude reuse: a prelude is now a clone of a `Kernel`
built once per process, restored only into a pristine kernel** (`WIP`,
kernel-reuse, 2026-08-15). Closes the longest-pending item on the refactor board
([`02-composition.md`](../../refactor-2026-08/02-composition.md) W1). Decision:
[ADR-0464](../../research/09-decisions/adr-0464-prelude-reuse-is-a-cloned-template-not-a-snapshot.md).

**No serialization, deliberately.** A snapshot format would put a *deserializer*
on the trusted path — code that can fabricate a `Declaration` the kernel never
checked. A clone cannot: the restored value is a bit-exact copy of a state the
caller could have reached themselves, so no new route into `Environment` exists.
The whole soundness argument reduces to one testable claim — prelude construction
is deterministic — which was already a public promise of `Kernel` and is now
load-bearing and tested.

**Speedups** (release, `taskset -c 0-7`, best of 9, same binary with
`AXEYUM_PRELUDE_CACHE` toggled): `nat` 26.09 -> **0.761 ms** (34x), `integer`
45.10 -> **2.244 ms** (20x), `logic` 1.53 -> 0.046 ms, `real` 1.62 -> 0.064 ms,
`string` 1.55 -> 0.163 ms. Debug (how `cargo test` runs): `nat` 261.6 -> 2.79 ms,
`integer` 421.7 -> 5.39 ms.

**Where the win is NOT — the board's premise was wrong, and this retires it
honestly.** `cargo test -p axeyum-lean-kernel` wall-clock is dominated by
`tests/nested_inductive_grammar.rs`, **84.9 s in a single test that builds no
prelude at all**, plus `kernel_seam_fuzz` at 25.2 s; all 265 lib unit tests
together take 4.7 s. Reuse removes real CPU (182.7 -> 98.9 s user on one A/B
pair) but the suite's critical path is a serial non-prelude test, so wall-clock
moves only ~110 -> ~106 s. A **one-shot process gains little** because it must
build the template it then clones — the inventory examples move 1.6x, 1.2x, or
not at all. The genuine win is in processes that build many kernels: the
solver's evidence path (`lean_crosscheck`, six per-query reconstruction routes)
measured **-29% wall / -27% CPU**.

**Instrumented, not estimated.** One `cargo test -p axeyum-lean-kernel` run
constructs **1,870 preludes** — `Logic` 1,731, `Nat` 85, `Int` 22, `Real` 17,
`String` 15. `Logic` dominates by count and was the least-discussed prelude; the
board's focus on `nat`/`integer` was on the expensive singles, not the frequent
ones.

**The soundness gate is a gate, not an assertion.** Ten tests compare a restored
kernel against an uncached build on the whole exported environment
(`render_lean4export_ndjson`), plus declaration inventory, trusted surface and
registered package. `scripts/check-prelude-reuse-equivalence.sh` repeats it
across processes on seven examples (byte-identical stdout/stderr/exit) and
requires the reuse counters to prove the flag was honoured in *both* directions,
so a typo cannot make it compare a run to itself. **Negative control exercised:**
corrupting the template made 6 of 10 tests fail, then it was removed. Invariants
hold exactly — `nat` axiom=0, `logic` axiom=0, `integer` trusted surface=1,
`real`=30, `string`=1, 119 Nat theorems.

**Two pre-existing defects found on the way, both of the "prints but does not
assert" family the coordinator flagged.**

1. `prelude_axiom_inventory` **was panicking on committed `HEAD`** (exit 101): it
   asserts `integer` has 34 axioms and the Int development has since been proved
   down to **1**. Fixed to 1. Nothing noticed because nothing checked its status.
2. Consequently **the committed Lean axiom ledger is stale**: `integer 34` is
   still baked into `scripts/gen-lean-axiom-ledger.py`'s trust policy, its test,
   `roadmap.md`, `prover-track/SYNTHESIS.md` and five other docs. The real total
   is **32, not 65** (real 30 + integer 1 + string 1). `gen-lean-axiom-ledger.py
   --check` now exits 1 with an accurate message instead of crashing opaquely.
   **This understates the project's own achievement and is not mine to change** —
   the count is bound by
   [ADR-0388](../../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md),
   whose publication rule requires it. Needs a superseding ADR plus a ledger
   regeneration. **Next owner of the ledger should take this first.**

**Exit codes on the inventory examples**, per the coordinator's audit. A named
theorem that matches nothing now exits non-zero (`nat_theorem_inventory`,
`int_theorem_inventory`); `nat_axiom_inventory` gained `--require-axiom-free
<prelude>` and `--expect-axioms <prelude>=<n>`, both of which **fail if the named
prelude was never enumerated** rather than passing on absence. Also
`--expect-count`, `--expect-derived`, `--expect-asserted`. Thirteen positive and
negative cases verified by hand. Flag spellings for the ledger wiring:

```
nat_theorem_inventory  [FILTER] [--expect-count N]
int_theorem_inventory  [FILTER] [--expect-derived N] [--expect-asserted N]
nat_axiom_inventory    [--require-axiom-free PRELUDE] [--expect-axioms PRELUDE=N]
```

**Not done, deliberately.** `scripts/check-prelude-reuse-equivalence.sh` is not
registered in `scripts/check.sh` or the `justfile`: both had uncommitted edits
from other lanes, and this repository has lost work five times to two lanes
touching one file. It is committed and runnable; registering it is one line for
whoever owns those files next.

**Next for this lane.** Convert the six `axeyum-solver` reconstruction routes to
share one long-lived kernel rather than one per query — reuse makes each
`Kernel::new()` cheap, but the routes still rebuild per query and the remaining
cost is now the clone rather than the build. Then decide whether `Kernel: Clone`
should become public API (ADR-0464 deliberately left it private).

<!-- plan-section: landed-changes -->

| 2026-08-15 | `PENDING` | Process-wide prelude reuse (ADR-0464): a prelude is a clone of a `Kernel` built once per process, restored only into a kernel observably identical to `Kernel::default()`. No serialization, so no deserializer on the trusted path. `nat` 26.09 -> 0.761 ms, `integer` 45.10 -> 2.244 ms; solver evidence path -29% wall. Ten equivalence tests comparing whole exported environments, a cross-process byte-identical gate with counter liveness, and an exercised negative control. Found and fixed a `prelude_axiom_inventory` panic on `HEAD` (asserted integer=34, actual 1) and gave the three inventory examples real exit codes. |
