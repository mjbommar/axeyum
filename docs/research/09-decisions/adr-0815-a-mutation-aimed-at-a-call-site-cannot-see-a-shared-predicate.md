# ADR-0815: A mutation aimed at a call site cannot see a shared predicate

Status: accepted
Date: 2026-08-30
Index-summary: All four ADR-0780 mutant survivors are closed. Three were ONE failure mode -- a guard removed at a call site while a second implementation of the same predicate still rejects, measured by disabling both and watching the kernel admit a non-positive inductive -- and only `literals` was a real corpus gap. The kill table is now 8 killed / 0 survived over a 35-case corpus, each new case flipping exactly one case to P0; `reduce_quotient`'s `mk` name check is recorded as unkillable by construction rather than covered by a case that could not discriminate.

Lane: `kernel-mutant-survivors`. Supersedes in part
[ADR-0780](adr-0780-the-kernel-differential-corpus-finds-real-defects-and-two-guards-survive-uncaught.md);
context is
[ADR-0717](adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md)
risk 1.

## Context

ADR-0780 built the kernel differential against pinned Lean 4.30.0 and found
zero Axeyum-accepts/Lean-rejects disagreements across 32 cases in eight
subsystems. It also mutation-tested the kernel itself, one mutation per
subsystem, and four of the eight mutants **survived**: the corpus did not
notice that a soundness guard had been removed.

That is the shape ADR-0717 risk 1 warns about. A differential that cannot see
a removed guard is a differential whose green is uninformative about that
guard. Three survivors carried a named reason; the `inductives` one carried
none — "not yet root-caused", the most important open item in L0.

## Decision

**Aim a kernel mutation at the guard nothing else reproduces, not at the guard
whose name matches the subsystem.** Where two implementations of one predicate
exist, mutate the predicate. Where a validator has one clause that nothing
downstream repeats, mutate that clause. And record the redundancies rather than
deleting them: they are real defence in depth *and* they are the reason a naive
per-guard mutation score over this kernel reads low.

Concretely, `artifacts/kernel-differential/mutant-kill-table.json` now carries,
per subsystem, the mutation that kills plus a `superseded_mutation` block naming
the one that survived and why — and a `redundancy_findings` section stating each
redundancy as a claim with its evidence.

## What the measurements were

All in an isolated lane worktree, `--release`, one kernel rebuild per row, the
corpus re-run against the pinned toolchain each time.

### `inductives` — three outcomes were possible; it was the first

The brief allowed three answers: a different real guard rejects; nothing
rejects and the case never discriminated; or positivity is not load-bearing at
all. It is the first, and the mechanism is worth more than the verdict.

| # | kernel state | `add_inductive(Bad, …)` returns |
|---|---|---|
| E1 | unmutated | `Err(NonPositiveInductiveOccurrence { field_index: 0 })` |
| E2 | positivity `Err` off (`inductive.rs:1933`) — ADR-0780's mutation | `Err(ReflexiveOrNestedNotSupported)` |
| E3 | field-shape classification off (`inductive.rs:2076`) | `Err(NonPositiveInductiveOccurrence)` |
| E4 | **both off** | **`Ok(())`** — P0 |
| E5 | shared predicate `mentions_group_family`'s `Const` arm forced `false` | **`Ok(())`** — P0 |

E1 answers what ADR-0780 could not rule out: the case *does* reach the guard the
mutation targeted. E2 names the guard that takes over,
`classify_bad_group_recursive_field` (`inductive.rs:2225`), reached from
`check_group_ctor`'s `else if mentions_group_family(domain, group)`. E3 shows the
redundancy is symmetric. **E4 is the one that matters**: with both gone the
kernel admits a non-positive inductive that Lean rejects, so the pair is jointly
load-bearing and neither half is decoration.

Reading the two: `check_group_positive_occurrence` (`inductive.rs:1917`) and
`open_group_recursive_field_shape` (`inductive.rs:2125`) are the same algorithm
written twice — whnf, walk Pi binders, stop when a binder domain mentions a
family, accept iff the head is a valid family application with the right
parameters and family-free indices. One returns `Some` exactly where the other
returns `Ok`. They differ only in which `KernelError` they name.

So **no corpus case can separate them; the separation does not exist.** The
instruction to "add a case that genuinely needs positivity" is unsatisfiable for
a single-site mutation, and that impossibility is the finding.

### `projections` — same shape, different pair

ADR-0780 correctly identified that the explicit `field_index >= field_count`
bounds check is redundant with `infer_projection`'s own field walk (`field_count`
is the constructor's `num_fields` metadata; the walk consumes the constructor
type's Pi telescope, and `add_inductive` derives one from the other). What it left
open is that no case in the 32-case corpus could kill *any* single projection
guard.

The new case targets `constructor_count != 1` → `ProjectionConstructorCount`, the
one clause of `projection_inference_data` nothing downstream repeats: a projection
from a **two-constructor** inductive, at field 0 of the first constructor, which is
in-bounds and well-formed so every other guard in the function passes. With the
count check gone, the walk succeeds and hands back the first constructor's field
type — a value extracted from something that may have been built with the *other*
constructor. Lean names the same guard: *"Projections extract constructor fields
for one-constructor inductive types … `Choice` … is not a one-constructor
inductive type."*

### `literals` — the one genuine corpus gap

ADR-0780's named reason was right and complete: every literals case used
`build_logic_prelude`'s correctly-shaped `Nat`, so none reached the bootstrap
validator's failure path. The **same** mutation now kills, with only the corpus
changed. The new case declares its own `Nat` whose `succ` takes two arguments and
satisfies every other clause of the contract, so only `succ_ok`'s `num_fields: 1`
clause rejects. It is soundness-relevant: `reduce_nat_succ` and
`reduce_nat_binop` compute over a literal by treating `succ` as unary.

### `quotient` — the named reason was *stronger* than stated

ADR-0780 said the corpus builds one quotient package per kernel, so
`reduce_quotient`'s `is_named_quotient_member(constructor_name, "mk")` sub-check
never sees a rival. That is true and understated. **A second `mk`-shaped
constructor is unconstructible.** `Kernel::add_quotient_package` is the only route
by which a `Declaration::Quotient` reaches the environment — the sole non-test
`env.insert_unchecked` of one is `quotient.rs:90`, inside that function's own
transaction — and it validates candidate names against `quotient_names()`, which
hard-codes `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind`. So no corpus case can ever
discriminate that sub-check, and none is written pretending to.

The mutant is aimed at `validate_quotient_package`'s per-declaration type contract
instead. Isolating it took two attempts, and the first attempt is instructive:
merely **exchanging** `Quot`'s and `Quot.mk`'s types produces a candidate that is
not well-typed at all (`Quot.mk`'s type mentions `Quot`, absent from the
environment when declaration 0 is checked), so the transaction's own
`check_declaration` rejects it — measured, that version stayed `AgreeReject`
under the mutation. The redundancy trap catches you *twice* if you are not
looking for it.

The case that works is a package that is completely well-typed and internally
consistent and simply is not Lean's: `Quot.lift` with its respectfulness
hypothesis deleted, names, kinds, order and universe arities untouched. That is
the canonical unsound eliminator, and the type contract is the only thing between
it and admission.

## Consequences

- Kill table: **8 killed, 0 survived**, over a 35-case corpus. Each of the three
  new cases flips **exactly one** case, to P0.
- Three redundancies are recorded as first-class findings with their evidence,
  not folded into prose. Two are ordinary defence in depth (`R1` inductives,
  `R2` projections); one is defence against a state the public API cannot produce
  (`R3` quotient), which is worth keeping and honestly unmeasurable today.
- **No P0 disagreement exists in the unmutated kernel.** Every P0 above is an
  artefact of a deliberately mutated kernel; the source was restored
  byte-identical to its backup before each commit.

## What this still cannot see

The differential compares **accept/reject on a whole declaration**, so it is
blind to a kernel that accepts the right things for the wrong reason —
in particular to a defect in a predicate *both* implementations share and that
`mentions_group_family`'s `Const` arm does not cover (its `Proj`/`Let`/`App`
arms are exercised by nothing in this corpus). Mutation measures the guards
that exist; it says nothing about a guard never written, which is the standing
limitation recorded for `nra_monomial_bound_cert.rs` and applies here verbatim.

ADR-0780's uncovered list is otherwise unchanged and deliberately so: mutual and
nested inductives, indexed families beyond 0-index, Prop-restricted large
elimination, structure eta beyond plain projection, string literals, zeta
reduction, well-founded recursion, and longer reduction chains. This lane added
three cases and no more, because a case that does not change a mutant's outcome
is decoration, and each of these three is shown to change one.

## Reproduction

```sh
cargo test -p axeyum-lean-kernel --release --test kernel_differential -- --nocapture
python3 scripts/check-kernel-differential-mutants.py
```

The mutation rows are reapplied by hand, one at a time, in an isolated worktree —
never the shared checkout, where a mutant on disk breaks every other lane's build
and looks like their bug. `crates/axeyum-lean-kernel/tests/kernel_differential_probe.rs`
prints the concrete `KernelError` a construction produces, which is what makes it
possible to aim a mutation at the guard a case *reaches* rather than the guard its
name suggests.
