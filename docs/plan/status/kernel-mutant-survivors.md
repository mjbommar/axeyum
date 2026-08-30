# Lane: kernel-mutant-survivors

**Status:** IN PROGRESS — `inductives` survivor EXPLAINED and re-aimed; the
three named-reason survivors are next.

## Charter

Close the four SURVIVED entries in
`artifacts/kernel-differential/mutant-kill-table.json` (ADR-0780, ADR-0717 S5).

## Finding 1 — the `inductives` survivor is explained (outcome 1, plus more)

**Outcome: a different real guard rejects the case. The mutation was aimed at
one of TWO redundant implementations of the same predicate.**

Measured in this worktree with `tests/kernel_differential_probe.rs`, a
diagnostic that prints the concrete `KernelError` the kernel returns for the
exact construction behind `inductives::non_positive_occurrence_negative`
(`Bad.mk : (Bad -> Codomain) -> Bad`). Five runs, one kernel rebuild each,
all `--release`:

| # | kernel state | `add_inductive(Bad, ...)` returns |
|---|---|---|
| E1 | unmutated | `Err(NonPositiveInductiveOccurrence { field_index: 0 })` |
| E2 | positivity `Err` off (`inductive.rs:1933`) — **ADR-0780's mutation** | `Err(ReflexiveOrNestedNotSupported)` |
| E3 | field-shape classification off (`inductive.rs:2076`) | `Err(NonPositiveInductiveOccurrence)` |
| E4 | **both off** | **`Ok(())`** — Axeyum accepts, Lean rejects: P0 |
| E5 | shared predicate `mentions_group_family`'s `Const` arm forced `false` | **`Ok(())`** — P0 |

E1 settles the first question ADR-0780 left open: the case *does* reach the
guard the mutation targeted. E2 names the guard that takes over —
`classify_bad_group_recursive_field` (`inductive.rs:2225`), reached from
`check_group_ctor`'s `else if self.mentions_group_family(domain, group)`
at `inductive.rs:2076`.

E3 shows the redundancy is **symmetric**: removing either one leaves the
other rejecting. E4 shows the pair is **jointly load-bearing** — remove both
and the kernel admits a non-positive inductive, which is exactly the P0
signal the mutation was supposed to produce.

### Why they are redundant: the same algorithm, written twice

`check_group_positive_occurrence` (`inductive.rs:1917`) and
`open_group_recursive_field_shape` (`inductive.rs:2125`) implement the same
predicate over a constructor field type, by the same walk:

- whnf; walk Pi binders; stop as soon as a binder **domain** mentions a family
  in the group;
- accept iff the remaining head is a `valid_group_family_application` with the
  right parameter values and family-free indices.

`open_group_recursive_field_shape` returns `Some` on exactly the field types
`check_group_positive_occurrence` returns `Ok` on, and `None` on exactly those
it returns `Err` on. They differ only in the `KernelError` variant they name
(`NonPositiveInductiveOccurrence` / `InvalidInductiveOccurrence` versus
`ReflexiveOrNestedNotSupported` / `RecursiveInductiveNotSupported`).

**No corpus case can separate them**, because the separation does not exist:
they agree on every field type by construction. Adding "a case that genuinely
needs positivity" is therefore impossible for a single-site mutation — that is
the finding, not a corpus gap.

### The generalizable lesson

Mutation at the **call site** cannot see a defect in a **shared predicate**.
Both call sites were individually removable with the corpus still green; the
predicate they share was not. E5 is the correctly-aimed mutation: one edit,
one subsystem, KILLED, with a real P0 kill signal.

So the `inductives` entry in the kill table is re-aimed from
`check_group_positive_occurrence`'s `Err` branch to `mentions_group_family`'s
`Const` arm, and moves SURVIVED -> KILLED. The old aim is retained in the
artifact as a recorded redundancy finding rather than deleted.

**No P0 disagreement exists in the unmutated kernel.** Every P0 above is an
artefact of a deliberately mutated kernel, and the source was restored
byte-identical to its backup (`diff -q` exit 0) before this commit.

## Next

- `projections`, `literals`, `quotient` survivors — corpus gaps with named
  shapes.
