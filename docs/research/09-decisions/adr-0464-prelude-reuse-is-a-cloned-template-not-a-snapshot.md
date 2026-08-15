# ADR-0464: Prelude reuse is a cloned in-process template, not a serialized snapshot

Status: accepted
Date: 2026-08-15
Index-summary: Reuse built preludes by cloning a once-built `Kernel` template on a pristine kernel; no serialization, so no deserializer on the trusted path
Index-status: accepted

## Context

Every consumer of the Lean kernel rebuilds its prelude declaration by
declaration. Measured on this tree (release, `taskset -c 0-7`, best of 9):

| prelude | build |
|---|---|
| `nat` | 26.09 ms |
| `integer` | 45.10 ms |
| `logic` | 1.53 ms |
| `real` | 1.62 ms |
| `string` | 1.55 ms |

In `cargo test` (debug) the same builds cost **261.6 ms** (`nat`) and **421.7 ms**
(`integer`).

The cost is paid often. Instrumenting `Kernel::register_prelude` over one
`cargo test -p axeyum-lean-kernel` run counted **1,870 prelude constructions**:

| prelude | constructions |
|---|---|
| `Logic` | 1,731 |
| `Nat` | 85 |
| `Int` | 22 |
| `Real` | 17 |
| `String` | 15 |

There are 142 `build_*_prelude` call sites across the workspace, and the existing
`cached_prelude` mechanism (ADR-0387) is **per-`Kernel`**: a second build inside
one kernel is a lookup, a fresh kernel pays in full. Since `build_int_prelude`
builds `nat` first, every theorem the library gains makes every fresh-kernel
reconstruction more expensive — a tax that grows in proportion to the
mathematical progress that is the point of the project
([`docs/refactor-2026-08/02-composition.md`](../../refactor-2026-08/02-composition.md),
item W1).

The blocking question was never whether to reuse, but **how to reuse without
weakening the trusted surface**. This kernel's headline claim is axiom-freedom
measured by `Kernel::axiom_footprint`; a reuse mechanism that could admit a
declaration the type checker never saw would invalidate it.

## Decision

**A prelude is reused by cloning a `Kernel` that was built once per process
through the ordinary trusted gate, and only into a kernel that is observably
identical to `Kernel::default()`.**

Concretely (`crates/axeyum-lean-kernel/src/prelude_cache.rs`):

- Each of `Logic`, `Nat`, `Int`, `Real` has a `OnceLock<Option<Kernel>>`
  template, built by the *uncached* builder on a fresh `Kernel`. `None` records
  that the build failed, so callers fall through and observe the same error.
- `try_restore(kernel, key)` replaces `*kernel` with `template.clone()` **only
  if** `kernel.is_pristine()`. Both `Kernel::is_pristine` and
  `Environment::is_pristine` destructure every field, so adding a field without
  revisiting the predicate is a compile error.
- `Environment::is_pristine` is strictly stronger than `is_empty`: an
  environment emptied by rollback has a moved `revision` and a non-empty
  `insertion_log`, and must not be silently replaced.
- `String` preludes get no template. They require a caller-held `LogicPrelude`
  and so never start pristine; their marginal cost over `Logic` is ~0.5 ms,
  which the `Logic` template already collects.
- `AXEYUM_PRELUDE_CACHE=0` forces every caller onto the ordinary path, for
  differential testing only.

**Nothing is serialized.** This is the load-bearing half of the decision: a
snapshot format would put a *deserializer* on the trusted path, i.e. code that
can fabricate a `Declaration` the kernel never checked. A clone cannot. The
restored value is a bit-exact copy of a state the caller could have reached
themselves — the state immediately after running the same builder on a fresh
`Kernel` — so no new route into `Environment` exists at all.

The entire soundness argument therefore reduces to one testable claim:

> Prelude construction is a deterministic function of the empty kernel, so the
> template equals what a fresh build would have produced.

That is already a public promise of `Kernel` (dense ids assigned in insertion
order; identical construction sequences are reproducible). This ADR makes it
load-bearing, and tests it rather than asserting it.

## Evidence

**Equivalence, in-process** (`src/prelude_cache/prelude_cache_tests.rs`, 10
tests). For each of `Logic`/`Nat`/`Int`/`Real`, one kernel is built through the
uncached builder and another through the template, and the two must agree on:
the registered `PreludeValue`; the declaration count; the full declaration
inventory (name, kind, rendered type, in environment order); the trusted surface;
and `render_lean4export_ndjson` of the **whole environment** — every declaration,
universe, type and proof body, in a deterministic order.

**Equivalence, cross-process** (`scripts/check-prelude-reuse-equivalence.sh`).
Seven inventory examples must produce byte-identical stdout, stderr and exit
status with reuse on and off. Measured: `compared=7 failures=0`.

**Negative control, exercised not asserted.** Corrupting `template()` to admit
one extra inductive made **6 of the 10** tests fail, `logic` failing precisely on
`declaration count differs`. The corruption was then removed and all 10 pass.
Without this, the equivalence tests would be indistinguishable from tests that
check nothing.

**Mutation independence.** `mutating_a_restored_kernel_cannot_affect_a_later_restore`
admits a marker inductive into a restored kernel and requires a later restore to
be unaffected *and* the mutated kernel to keep its own mutation — independence in
both directions, not defensive re-cloning.

**Liveness.** `prelude_cache::stats()` reports hits/misses/templates. The
differential gate requires the cache-on run to report `hits>0` and the cache-off
run `hits=0`, so a typo in the environment variable cannot make the gate compare
a run to itself. Measured: on `hits=13 misses=0 templates_built=4`, off `hits=0
misses=18 templates_built=0`.

**Invariants held.** `nat` axiom=0, `logic` axiom=0, `integer` trusted surface=1,
`real`=30, `string`=1, and 119 Nat theorems — all unchanged under reuse, and now
pinned by tests and by new example flags rather than printed.

**Performance** (release, `taskset -c 0-7`, best of 9; same binary, cache toggled
by environment variable):

| prelude | build | reuse | speedup |
|---|---|---|---|
| `nat` | 26.09 ms | 0.761 ms | 34x |
| `integer` | 45.10 ms | 2.244 ms | 20x |
| `logic` | 1.53 ms | 0.046 ms | 33x |
| `real` | 1.62 ms | 0.064 ms | 25x |
| `string` | 1.55 ms | 0.163 ms | 9.5x |

Debug (how `cargo test` runs): `nat` 261.6 -> 2.79 ms, `integer` 421.7 -> 5.39 ms,
`logic` 13.76 -> 0.18 ms.

**Where the win is NOT.** Honest scoping, since the board item assumed otherwise:
`cargo test -p axeyum-lean-kernel` wall-clock is dominated by
`tests/nested_inductive_grammar.rs` (**84.9 s in a single test that builds no
prelude at all**) and `tests/kernel_seam_fuzz.rs` (25.2 s); all 265 lib unit tests
together take 4.7 s. Reuse removes CPU work (measured 182.7 s -> 98.9 s user time
on one A/B pair) but the suite's critical path is a serial non-prelude test, so
wall-clock improves only ~110 s -> ~106 s. Likewise a **one-shot process gains
little**, because it must build the template it then clones: the inventory
examples move 1.6x, 1.2x, or not at all. The large wins are in processes that
build many kernels — the test suites, and the six per-query reconstruction routes
in `axeyum-solver`.

## Alternatives

**A serialized prelude snapshot** (build once, persist, load). Rejected on
soundness, not effort: it puts a deserializer on the trusted path, so the kernel
would need to re-check what it loads (recovering the cost) or trust a parser
(losing the claim). The clone has the same benefit with no new trusted code.

**Structural sharing of the declaration store** (`Arc` behind the `Kernel`).
Rejected for now: it makes the shared state genuinely shared, so the negative
test above becomes a *hazard to design against* rather than a property that holds
by construction. Cloning is O(size of prelude) and already 20-90x cheaper than
rebuilding; sharing optimizes a cost that is no longer dominant. Revisit only if
clone cost becomes measurable against query time.

**Making `Kernel: Clone` public.** Deliberately not done. `Clone` is derived but
the public surface gains only `prelude_cache::{stats, enabled, PreludeCacheStats}`.
Widening the kernel's public API is a separate decision, and the documented rule
that handles must not be mixed across kernels deserves its own treatment before
handing callers a second kernel with identical ids.

**Changing the call sites** to a `Kernel::with_nat_prelude()` constructor.
Rejected: 142 call sites, and the transparent fast path is observationally
identical, so the churn buys nothing.

## Consequences

- Reuse is transparent: no call site changed, and `build_*_prelude` keeps its
  exact signature and error behaviour.
- The determinism promise on `Kernel` is now **load-bearing** rather than
  aspirational. A future non-deterministic construction step (hash-map iteration
  order reaching a builder) becomes a correctness bug caught by the equivalence
  tests, which is the right place to catch it.
- Templates live for the process lifetime. Four kernels' worth of arenas is the
  memory price of never rebuilding them; a process that never uses a prelude
  never builds its template.
- `Environment::is_pristine` exists and must stay strictly stronger than
  `is_empty`.
- Any new prelude gets reuse by adding a `Slot`, an uncached builder, and a case
  in the equivalence test — the test is parameterized over `PreludeKey` for
  exactly that reason.
- **Not done here:** wiring `scripts/check-prelude-reuse-equivalence.sh` into
  `scripts/check.sh` and the `justfile`. Both files had uncommitted edits from
  other lanes at the time, and this repository has lost work five times to two
  lanes touching one file. The gate is committed and runnable; registering it is
  a one-line change for whoever owns those files next.
