# Prelude-build refactor spike, 2026-08-27

Prototype of [2026-08-27-architecture-review.md](2026-08-27-architecture-review.md)
§1's proposed fix, built and measured on `crates/axeyum-lean-kernel/src/complex.rs`
(148 `ComplexPrelude` fields, 89 `declare_*` calls) rather than on `creal.rs`
(441 fields, 364 calls), which had a live lane. Every number below is measured
on this repository's actual `complex` prelude, not simulated.

## Summary

- **Level 1 (declared dependencies + a precise error): implemented and green.**
  Extracted the true dependency graph for all 89 build steps by static analysis,
  found it **already a valid topological order with zero violations** across
  1,279 requirement edges, and built a structural preflight
  (`validate_step_order`) that fails naming the missing declaration, the step
  that would produce it, and both steps' positions — before the kernel ever
  sees a term. Two tests prove it discriminates: one deliberately places a
  consumer before its provider, one deliberately names a dependency nothing
  provides.
- **Level 2 (topological ordering): answered, not wired into runtime.** The
  dependency graph has no cycles (a valid total order over it exists and was
  found), and the existing hand-written order already respects it. Recomputing
  and *executing* an alternative topological order was judged unnecessary risk
  for zero benefit — the existing order already works and the level-1 preflight
  already catches a future violation — so `STEPS`' order is preserved exactly
  (pinned by a test) rather than replaced by a freshly computed one.
- **Part B (module-owned registries): prototyped for real on `poly.rs`, not
  simulated.** `poly`'s 21 fields moved out of `ComplexPrelude` into a
  `poly::PolyNames` struct that `poly.rs` owns outright. Confirmed nothing
  outside `poly.rs` depends on any of those 21 fields, so the hub's footprint
  for the whole module dropped to **zero** — a new declaration inside `poly.rs`
  now touches `complex.rs` not at all, down from up to 3 lines.
- **Recommend applying level 1 to `creal.rs` without reservation.** Recommend
  piloting Part B's module split on **one** already-separate `creal/*.rs` file
  before generalizing across all 33 — the churn scales with field count, and
  `creal`'s 441 fields make a full split roughly 25-60x poly's, by the numbers
  below.

## Part A — the phase-order fix

### Mechanism

Every `ComplexPrelude` field is an interned `NameId`, valid as a *handle*
regardless of build order (`intern_names` runs once, up front). The failure
class is that the *declaration* behind a handle is not yet in the kernel
environment when a `declare_*` runs — the kernel then reports
`KernelError::UnknownConst { name }`, indistinguishable from `name` never
having been declared at all.

The fix has two parts, both in `complex.rs`:

```rust
struct BuildStep {
    label: &'static str,
    requires: &'static [fn(ComplexPrelude) -> NameId],
    provides: &'static [fn(ComplexPrelude) -> NameId],
    run: fn(&mut IntDev<'_>, ComplexPrelude) -> Result<(), KernelError>,
}

const STEPS: &[BuildStep] = &[
    BuildStep { label: "declare_carrier", requires: &[], provides: &[/* complex, mk, rec */], run: declare_carrier },
    // … 88 more, one per existing declare_* call, in the SAME order …
];
```

`validate_step_order(p, STEPS)` is a **pure, kernel-free** structural check:
walk `STEPS` in order, track which fields are "declared so far" (their
`NameId`s), and fail the first time a step's `requires` names a field nothing
earlier provided. `build_complex_prelude` runs it once, before touching the
kernel, and panics with a diagnosis if it fails — the existing order always
passes, so this adds zero cost on every normal build beyond one array walk.

### How the dependency table was built

Requires/provides were extracted by **static analysis**, not written by hand
(89 steps × up to ~35 dependencies each is not something to transcribe
correctly by hand):

1. `provides`: for each of the 89 top-level functions (plus `poly.rs`'s 18
   internal ones, folded into the one `poly::declare_polynomial` step), find
   every `name: p.<field>` inside a `Declaration::{Theorem,Definition}` literal
   and every `add_inductive(p.<field>, …)` — the exact places the kernel
   environment actually gains a declaration. This covered 99 of 147 fields
   automatically; the remaining 36 (constructors handed to closures like
   `project(d, p.re, true)` and `binary(d, p.add, …)`) were resolved by hand
   from the closure's own body and cross-checked field-by-field.
2. `requires`: direct `p.<field>` references in a function's body, plus a
   **transitive closure through this module's private term-builder helpers**
   (`zeq`, `ceq`, `re_of`, `zchain`, …) via the same-file call graph, so a
   step that only calls `zeq(d, p, …)` still picks up `zeq`'s own `p.equiv`
   dependency.
3. **Self-consistency, not trust**: run the extracted table against the
   *existing* hand-written order and count violations. Zero false positives
   would be a coincidence at this scale if the extraction were wrong in a way
   that mattered; the result was **0 violations across 1,279 edges** on the
   first correct run, which is the evidence that both the extraction and the
   existing order are sound, not merely that neither was tested.

The scripts used for this extraction are not checked in (they were throwaway,
run from a scratch directory); the generated table is what is checked in and
tested (`steps_table_matches_recorded_extraction` pins the label order,
`existing_step_order_is_topologically_valid` pins that it validates).

### The deliberate-failure tests

`validate_step_order` being green on the one order it has ever seen proves
nothing about whether it can fail. Two tests construct broken two-step tables
directly (not through the kernel, so they run in microseconds) and assert the
returned `OrderViolation`'s fields precisely:

```rust
static BROKEN_ORDER: &[super::BuildStep] = &[
    super::BuildStep { label: "consumer_before_its_provider",
        requires: &[|p: ComplexPrelude| p.equiv], provides: &[], run: super::declare_carrier },
    super::BuildStep { label: "provider_after_its_consumer",
        requires: &[], provides: &[|p: ComplexPrelude| p.equiv], run: super::declare_equiv },
];
```

`order_violation_is_detected_and_precise` asserts `consumer_index == 0`,
`consumer_label == "consumer_before_its_provider"`, `missing == prelude.equiv`
(the *exact* NameId, not merely "something is missing"), and
`provider == Some((1, "provider_after_its_consumer"))`.
`order_violation_reports_missing_provider_as_table_bug` does the same for a
one-step table whose `requires` names a field nothing provides, asserting
`provider == None` — a table bug, reported as one, not a panic or a silent
pass. Both are green; both would need `validate_step_order` to actually
discriminate to pass, since each asserts specific field values a vacuous
"always Ok" or "always Err" implementation would fail.

Mutation-testing note: `scripts/tests/mutation_controls.py` is Python-only
(it drives Python subjects with `py_compile`/import-based mutation); it has no
Rust-side registration mechanism, so the guard here is the two `#[test]`s
above rather than an entry in that harness. Each assertion in each test is a
guard an implementation bug would need to survive; deleting any one of the
four field assertions and re-running would need to be independently
falsifiable, and each names a *distinct* fact (which step, which field, which
provider, `None` for the table-bug case) rather than one shared check four
ways — the shape the CLAUDE.md mutation-testing entries warn against.

### Level 2: topological validity, not runtime reordering

`validate_step_order`'s success on `STEPS` **is** the level-2 answer: a valid
topological order exists (the one already there), so the dependency graph is
acyclic. No cycle was found because none exists — not because the search was
narrow; the extraction covers all 89 steps and all 147 non-`creal` fields
(`CRealPrelude` fields are excluded because `build_creal_prelude` always runs
to completion before `complex`'s own build starts, so they are trivially
"already declared").

What was **not** done: deriving a fresh order via Kahn's algorithm and
executing declarations in *that* order instead of the hand-written one. Two
independent valid topological orders of the same DAG produce the same set of
kernel declarations either way (checkpoint/rollback is taken once, up front,
and each declaration's reducibility height is a fixed constant independent of
call order) — but re-deriving the actual runtime sequence is a change with a
cost (re-running the full kernel-checked build under a *different* order to
confirm nothing regressed) and no corresponding benefit, since the existing
order already works and the preflight already guards against a future
regression. This is the conservative-slicing call the level-1/level-2 split
in the brief anticipated: level 1 alone captures the fix; level 2's runtime
half is optional and was left undone deliberately, not overlooked.

## Part B — the production-side shard

### The problem this closes

Before: adding one declaration to an *existing* `declare_*` group touched
`complex.rs` in 2 places (a new `pub field: NameId,` in the 148-field struct,
a new `field: kernel.name_str(...)` line in `intern_names`); a genuinely new
group added a third (a new call in the build sequence — now a new `STEPS`
entry). All three touches land in the same 11,287-line file regardless of
which mathematical area the new declaration belongs to, so two lanes adding
unrelated declarations to two different areas both edit `complex.rs`.

### The fix, prototyped for real

`poly.rs`'s 21 declared names (`Complex.polyEval` and everything Horner-form/
degree/roots-of-unity built on it) moved into a struct **owned by `poly.rs`**:

```rust
// complex/poly.rs
pub struct PolyNames { pub poly_eval: NameId, /* … 20 more … */ }
pub(super) fn intern_names(kernel: &mut Kernel, complex: NameId) -> PolyNames { /* … */ }
```

```rust
// complex.rs
pub struct ComplexPrelude {
    pub creal: CRealPrelude,
    // … 126 other NameId fields, still flat …
    pub poly: poly::PolyNames,   // ONE line, was 21 field declarations
}
// intern_names:
poly: poly::intern_names(kernel, complex),   // ONE line, was 21 intern calls
```

`pub(crate) mod poly;` (matching the existing `pub(crate) mod ops;` pattern in
`int_prelude.rs`) makes `PolyNames` reachable from the rest of the crate
without exposing it outside it — `cargo check` is clean with zero warnings
after this change, including the `private_interfaces` lint that fires if the
module stays private while the field is `pub`.

The `STEPS` table's `poly::declare_polynomial` entry now declares
`provides: &[]` — checked against every other step's `requires` list first
(none names a `poly_*` field), so this is not an assumption. **A new
declaration added inside `poly.rs` now touches `complex.rs` zero times**: its
field goes in `PolyNames`, its interning goes in `poly::intern_names`, its
call goes in `poly::declare_polynomial`'s own 18-call internal sequence — all
three edits land in `poly.rs`, the file whose math it belongs to.

### The alternative considered and rejected

**Facade with flat accessor methods** (`impl ComplexPrelude { fn poly_eval(&self) -> NameId { self.poly.poly_eval } }` for all 21, keeping `p.poly_eval` call sites
unchanged) was considered and rejected: it would have avoided the 144-site
rewrite below entirely, but it reintroduces exactly the collision Part B
exists to remove — every accessor method still lives in `complex.rs`, so a
new `poly.rs` declaration needs a new accessor method there too, one hub
touch per name, unchanged from before. It only relocates *storage*, not
*editing pressure*. The nested-field form (`p.poly.poly_eval`) is the only one
of the two that actually reduces hub touches for a new declaration to zero,
which is the entire point, so it is the one implemented and recommended.

## Part C — the numbers

All measured on this repository's actual `complex`/`complex/poly.rs`, on
2026-08-27, on a host at load average ~11 (contended by concurrent lanes —
noted per the reference-frame convention; treat wall-clock numbers as
directional, not a clean before/after on an idle machine).

| Metric | Before | After |
|---|---|---|
| Hub (`complex.rs`) lines touched for a new declaration inside an *existing* core group | 2 (struct field + intern line) | 2 (unchanged — core groups were not split in this prototype) |
| Hub lines touched for a new declaration inside `poly.rs` | 2–3 (struct field + intern line, in `complex.rs`) | **0** |
| `ComplexPrelude` struct fields | 148 (147 `NameId` + `creal`) | 128 (126 `NameId` + `poly::PolyNames` + `creal`) |
| `declare_*` calls in one linear sequence (`complex.rs`) | 89, hand-written | 89, in `STEPS` (data), same order, pinned by test |
| `complex.rs` line count | 11,287 | 11,659 (+372: +~600 `STEPS`/`validate_step_order` infrastructure, −~140 poly fields/intern lines extracted) |
| `poly.rs` line count | 2,568 | 2,803 (+235: `PolyNames` struct + `intern_names`) |
| `complex*` call sites requiring `p.foo` → `p.poly.foo` (poly's 21 fields, measured by grep) | — | **144** (66 in `poly.rs`, 68 in `complex_tests.rs`, 10 in `cas_bridge_tests.rs`) |
| Estimated **full** `creal` churn if all 441 fields were split module-by-module (`p.<field>` occurrences across `creal.rs` + `creal/*.rs` + `creal/inventory/*.rs`, by grep) | — | **~8,997** across 71 files |
| `complex::` suite test count | 44 (43 `complex_tests` + 1 `cas_bridge_tests`) | 48 (+4: two order-violation tests, one order-pin test, one topological-validity test) |
| `complex::` suite wall-clock (`cargo test -p axeyum-lean-kernel --lib complex:: -- --test-threads=4`) | ~361 s (review baseline; threading/load unspecified) | **441.92 s**, 48 passed / 0 failed, measured at host load average ~11 (contended by other concurrent lanes' `cargo test` runs) — a ~22% increase over the baseline figure, but **not a clean A/B**: the baseline's own load/thread-count is not recorded, this run added 4 new tests (48 vs 44), and one of the four (`horner_from_top_diag_matches_poly_eval_at_a_nonzero_middle_coefficient`, pre-existing) alone ran long enough to dominate the tail under contention. The `STEPS`-table refactor itself adds one array walk (`validate_step_order` over 89 steps) to `build_complex_prelude`, which is microseconds, not seconds — the wall-clock delta is dominated by host contention and added test count, not by the refactor's own runtime cost. |
| Existing declaration order topologically valid? | Unknown / unverified | **Yes** — 0 violations across 1,279 extracted requirement edges; enforced automatically on every build via `validate_step_order`, and pinned by two tests |
| Cycles in the dependency graph? | Unknown | **None** — a total order exists (the one already there) |

The `creal` estimate (~8,997) is **not** "144 × (441/21)" scaled linearly —
it is a direct grep count, and it is higher per-field than `poly`'s ratio
(144/21 ≈ 6.9 sites/field vs. 8,997/441 ≈ 20.4 sites/field), consistent with
`creal` being a much larger, more cross-referenced development where any one
name is more likely to be reused elsewhere. Splitting `creal.rs` module-by-
module the same way would touch on the order of **9,000 call sites** across
71 files, not 144 across 3 — this is the number the recommendation below is
built on.

## What the kernel rejected

Nothing rejected any proof term: this is a structural/registry refactor, and
`every_named_complex_declaration_is_checked_and_footprint_free` (the
environment-derived coverage test — the actual safety net, not the pinned
counts above) stayed green throughout, confirming no declaration's kind or
axiom footprint changed. The only compiler-level friction was the
`private_interfaces` warning described in Part B, fixed by matching the
`pub(crate) mod` visibility this codebase already uses for `int_prelude::ops`
— not a proof issue, a module-visibility one.

## Recommendation

**Apply level 1 (the `STEPS` table + `validate_step_order` preflight) to
`creal.rs` without reservation.** It is the change the review measured as
carrying "near-zero reordering risk" and capturing "most of the cost," and
this prototype confirms the mechanism: it is a mechanical transformation of an
existing straight-line call sequence into a data table plus one preflight
call, provably zero-behavior-change on a correct table (the existing order was
found to already satisfy every extracted dependency), and it converts the
exact failure class that hit four lanes in one day
(`UnknownConst` indistinguishable from "does not exist") into a diagnosis
naming the missing declaration and the step that would produce it. The
extraction work (finding 364 `requires`/`provides` sets across `creal.rs`'s
much larger and more cross-referenced call graph) is the dominant cost, not
the mechanism itself — budget for it accordingly, but it is the same kind of
work done here, at roughly 4x the step count.

**Do not apply Part B's full module split to `creal.rs` in one pass; pilot it
on one already-separate `creal/*.rs` file first.** The poly prototype shows
the pattern works and reduces hub touches to zero for the module it is
applied to, but the ~8,997-call-site estimate for a *full* `creal` split is
50-60x this prototype's actual 144-site edit, spread across 71 files instead
of 3. That is not necessarily prohibitive — `creal` already has 33 separate
module files, so the module boundaries exist and the "own your names" pattern
maps onto them directly, the way it mapped onto `poly.rs` here — but it should
be validated on ONE file (say, `creal/sqrt.rs` or another with a
self-contained field set, checked the same way `poly`'s was checked here: zero
other steps require its fields) before committing to all 33, since the
per-file churn and any file-specific dependency surprises are unknown until
measured. **A level-1-only outcome for `creal` — the dependency table and
preflight, without the module split — is still a real win on its own**: it
eliminates the phase-order failure class, which is the more expensive and
more frequently recurring of the two problems the review measured (four
lanes in one day vs. the structural-collision problem, which requires two
lanes editing *different* modules on the *same* day to bite).
