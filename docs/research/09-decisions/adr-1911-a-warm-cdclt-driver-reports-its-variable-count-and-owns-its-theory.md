# ADR-1911: A warm CDCL(T) driver reports its variable count, and a warm adapter owns its theory

Status: accepted
Index-summary: Two decisions that together unblock Phase B3 of the CDCL consolidation plan, plus one correction to that plan's own scoping. (1) **`NativeTheory::take_new_atoms` takes the driver's current variable count.** `axeyum_solver::native_cdclt::NativeTheoryAdapter` kept a private `next_var` and MIRRORED the core's growth, with a comment saying that keeps the map aligned "without the core having to report back". That is exact only while registration is the one thing that moves the core's count — true on a one-shot solve, **false on a warm one**, where `NativeIncrementalCdcl::add_clause` grows the namespace between solves with nothing telling the adapter, so atoms map onto variables that belong to other clauses. The theory cannot pull the count (the driver holds it mutably borrowed at that call), so the driver pushes it. MEASURED, and it corrects the note that found the bug: the failure is a **wrong verdict** — with the fix reverted the new guard reports `Unsat` for a satisfiable database — and the adapter's own `debug_assert_eq!(.., "variable indices are dense")` **does not fire**, in release OR in debug, because it compares two counters the adapter owns and a stale `next_var` keeps them consistent with each other. (2) **The adapter is generic over its theory by value, with `TheorySolver` implemented for `&mut T`**, so the one-shot route instantiates `NativeTheoryAdapter<&mut Theory>` and a warm route `NativeTheoryAdapter<Theory>`; `NativeIncrementalCdcl` owns its theory, so a session holding both as sibling fields is a self-referential struct and not expressible. Driver-side atom registration is added as `WarmNativeCdclT::add_theory_variable` (`reserve` + `NativeTheoryAdapter::register_atom_variable`), because the theory-side channel `take_new_atoms` is polled INSIDE a solve and cannot hand an index back to a caller still building the clause the variable belongs to — and `EufTheory` does not implement it at all. (3) **Correction to the plan.** B3 was scoped as "a swap once B2 exists"; it was not, and B4's stated blocker list is also wrong in one place: the plan says dormant variables "do not exist in `axeyum-cnf` in any form", but `NativeIncrementalCdcl::reserve` already creates non-branchable variables and `add_input_clause` marks a literal's variable branchable, which is exactly `CdclT::add_theory_variable` + `add_permanent_clause`'s `activate_variables`. `qinst_egraph` is migrated on that basis and measured verdict-invariant, give-up-reason-invariant and model-validity-invariant on all 56 files of the two UF parity lists.
Date: 2026-09-10

## Context

Phase B3 of
[`docs/solver-comparison-2026-09/12-cdcl-consolidation-plan.md`](../../solver-comparison-2026-09/12-cdcl-consolidation-plan.md),
under [ADR-1908](adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md),
resting on [ADR-1909](adr-1909-warm-cdclt-is-one-theory-push-pop-scope-per-solve.md)
(warm CDCL(T) on the native core) and lane E3's measurement note
[`warm-cdclt-native-2026-09-10.md`](../03-measurements/warm-cdclt-native-2026-09-10.md).

The measurements for this ADR are in
[`qinst-egraph-native-b3-2026-09-10.md`](../03-measurements/qinst-egraph-native-b3-2026-09-10.md).

E3 ended its note with an obligation rather than a change:

> **B3's first obligation is to make the adapter read
> `NativeIncrementalCdcl::variable_count()` rather than mirror its own
> counter.** Not changed here, because the adapter is on the shipping one-shot
> route.

That is decision 1. Doing it exposed that B3 needed two more things, which is
decision 2, and that the plan's B3/B4 split rests on one wrong fact, which is
decision 3.

## Decision 1 — the driver reports where it will append

`NativeTheory::take_new_atoms` gains one parameter:

```rust
fn take_new_atoms(&mut self, next_var: usize) -> usize;
```

`next_var` is the driver's variable count at the moment of the call, which is
where `Cdcl::register_theory_atoms` appends the first of the atoms this call
reports. `NativeTheoryAdapter`'s private `next_var` field is deleted; the
adapter fills the gap below the reported index with `None` (those are the
non-atom variables `assert` must keep skipping) and appends from there.

### Why a parameter and not a getter

The theory cannot read the driver at this call: the driver reaches
`take_new_atoms` through `self.theory`, so the theory is mutably borrowed by
the object holding the count. Push, not pull. A theory whose atoms already
*are* variable indices ignores the argument, which is why the trait default
does.

### The measurement, and what it corrects

E3 established the defect by reading and predicted that the adapter's
`debug_assert_eq!(self.atom_for_var.len(), var, "variable indices are dense")`
is "what would fire — so the failure is **loud in debug and silent in
release**".

**The first half of that is wrong, and it matters, because it is the half that
would make somebody trust a debug test run.** The assertion compares
`atom_for_var.len()` against the index the adapter is about to push at, and
both come from the adapter's own bookkeeping: a stale `next_var` keeps them
consistent with each other while both run behind the core. Measured on the
fixture in
`native_cdclt::tests::a_warm_adapter_maps_a_late_atom_onto_the_variable_the_core_appended_it_at`,
with the fix reverted to the mirrored counter:

| profile | result | assertion raised |
|---|---|---|
| debug (default `cargo test`) | `Unsat` on a satisfiable database | **none** |
| `--release` | `Unsat` on a satisfiable database | **none** |

So the guard for this is a **verdict**, not an assertion, and the test is
written that way: it checks the verdict first, then the model's validity
against both the clauses and the theory rule, then the map itself. The
core-side pin
`atom_registration_survives_a_solve_boundary_and_appends_at_the_current_count`
additionally asserts that what the driver *reported* is where the variables
actually landed.

### Rejected

- **A shared counter handle** (`Rc<Cell<usize>>`, an `Arc<AtomicUsize>`) the
  driver writes and the adapter reads. Same information, one more object to
  keep in sync, and it re-creates the mirroring defect one level down: nothing
  makes the write happen.
- **Leaving the one-shot adapter alone and writing a second warm adapter.** Two
  copies of the atom↔variable translation, which is the one place in this
  module where a mistake is a wrong answer. The module header says it is "the
  single place that translation happens"; keeping that true is worth a trait
  parameter.

## Decision 2 — the adapter owns *or* borrows, and a warm route registers atoms through the driver

`NativeTheoryAdapter<'a, T>` held `&'a mut T`. `axeyum_cnf`'s
`NativeIncrementalCdcl<T>` **owns** its `T`, and `qinst_egraph`'s
`OnlineQuantifierClauseSession` holds its solver and its `EufTheory` as sibling
fields and reaches past the driver to the theory
(`EufTheory::add_atom_at_root`). A warm session would therefore have to hold a
struct borrowing its own field. Not expressible.

So: `TheorySolver` is implemented for `&mut T` (mirroring
`axeyum_cnf::theory::NativeTheory for &mut T`, at the same place in the stack
and for the same reason), and the adapter takes its theory **by value**:

| route | instantiation | why |
|---|---|---|
| one-shot (`solve_native`) | `NativeTheoryAdapter<&mut Theory>` | keeps the theory on its own stack and reads it back to assemble a model |
| warm (`WarmNativeCdclT`) | `NativeTheoryAdapter<Theory>` | the solver owns the theory; the route reaches it through `theory_mut()` |

One adapter, no lifetime parameter, and the one-shot call site is unchanged.

Atom registration is then two steps rather than one, behind
`WarmNativeCdclT::add_theory_variable`:

1. `NativeIncrementalCdcl::reserve(n + 1)` appends the variable
   **non-branchable**, exactly as `CdclT::add_theory_variable` appends it
   dormant;
2. `NativeTheoryAdapter::register_atom_variable(var)` claims it for the next
   atom and returns that atom's index.

It has to be driver-side. `NativeTheory::take_new_atoms` is polled by the core
at a propagation fixpoint *inside* a solve, so it cannot hand an index back to
a caller that is still building the clause the variable belongs to — and
`EufTheory` does not implement `take_new_atoms` at all (its `TheorySolver` impl
is `assert`, `push`, `pop`, `propagate` and nothing else), so for this theory
the poll channel returns `0` forever.

`NativeIncrementalCdcl::unwind_to_root` is added as the public counterpart of
`CdclT::backtrack_to_root`. It is needed, not cosmetic: the theory epoch closes
lazily so a model stays readable after a solve, and `add_atom_at_root` refuses
to run inside one, so without it the first registration of every batch would be
refused.

## Decision 3 — the plan's B3/B4 scoping is corrected

The plan says:

> **B3. `qinst_egraph`** after B2: it calls `backtrack_to_root` first thing,
> which is already the native between-solves discipline, so it is a swap once
> B2 exists.

It is not a swap. `backtrack_to_root` is the *easy* half; the route also calls
`CdclT::add_theory_variable`, which appears in neither the B3 nor the B4
description, and which needed decision 2.

And one blocker the plan attributes to B4 is not real:

> it needs dormant variables, which do not exist in `axeyum-cnf` in any form.

`NativeIncrementalCdcl::reserve` creates variables that are legal and **not
branchable** (`Cdcl::branchable` exists and starts `false`), and
`Cdcl::add_input_clause` marks a literal's variable branchable when the clause
arrives — which is precisely the `CdclT::add_theory_variable` (dormant) +
`add_permanent_clause` (`activate_variables`) pair. Whether B4's *mid-search*
insertion can use them is a separate question this ADR does not answer; the
claim corrected here is the absolute one.

## Consequences

- `qinst_egraph` runs on the native core. `CdclT` has **no remaining CDCL(T)
  client in `src/`**; its `backtrack_to_root` and `value` are retained under an
  `expect(dead_code)` naming ADR-1908 B5, because an oracle missing the
  incremental half of its protocol cannot adjudicate the route that used it.
  Deleting them is B5's call.
- `WarmNativeCdclT` is the `CdclT` surface a warm, root-only route uses, and it
  is where the three differences from `CdclT` live — two-step registration, a
  variable in no clause not being branchable, and the lazily-closed theory
  epoch — rather than being re-derived at each call site.
- Verdict invariance is **measured**, not argued, on all 56 files of the two UF
  parity lists, on three axes: verdicts per file, give-up reason strings per
  file, and evidence (a sat model replayed against a fresh parse of the
  original file). See the measurement note. Model *equality* is deliberately
  not claimed — E3 measured that a warm model is not a one-shot model and
  cannot be.
