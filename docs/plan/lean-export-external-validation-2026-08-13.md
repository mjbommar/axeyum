# The Lean export is not externally checkable yet — measurement, 2026-08-13

Closes the open question behind item A2 of
[next actions from the Rado paper](next-actions-from-the-rado-paper-2026-08-12.md),
which read:

> One command on any host with a toolchain converts *"we emitted a Lean module"*
> into *"an independent kernel accepted it."* Very high credibility per unit of
> effort, and it is the single cheapest item on this list.

The command was run. The answer is negative, and the reason is architectural
rather than a typo. Full reproduction:
`/nas3/data/axeyum/frontier-2026-08-13/coordinator/logs/lean-export-check-2026-08-13.md`.

## The toolchain was never absent

A2 records that `lean`, `lake` and `elan` are "all absent on the machine that
produced it (verified)". On s0 today:

```
$ which lean lake elan            # nothing
$ ls ~/.elan/toolchains
leanprover--lean4---v4.30.0
$ ~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean --version
Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit d024af09, Release)
```

`elan` is genuinely absent. The pinned toolchain — matching this repository's own
`lean-toolchain` (`leanprover/lean4:v4.30.0`) — was unpacked and working the
whole time, together with `lake`, `leanc` and `leanchecker`. `which` returning
nothing was read as a fact about the machine.

This belongs on the CLAUDE.md list of tools that lied: it is the same shape as
the pre-push hook that had never run because `core.hooksPath` was unset.

## The export is rejected

```
$ lean proofs/shell_closed_form.lean          # in ../axeyum-rado-paper
... 22 errors ...  EXIT=1   real 0m0.175s
```

Three causes, isolated by fixing each on a copy and re-running. The paper's
artifact was not modified.

1. **Codegen.** Recursor-based `def`s fail with "code generator does not support
   recursor `AxNat.rec`". They are proofs, not programs; they need
   `noncomputable`. Cosmetic.
2. **Self-reference with explicit universes.** `Eq.{u}` is emitted *inside*
   `Eq`'s own constructor. Lean rejects it ("`Eq` is a local variable"), the
   inductive never enters the environment, and 19 of the 22 errors are that one
   defect cascading — ending with `#print axioms shell_closed_form` unable to
   find its own subject.
3. **Parameters versus indices.** The emitter declares

   ```lean
   inductive Eq.{u} : ((x0 : Sort (u)) -> ((x1 : x0) -> ((x2 : x0) -> Prop)))
   ```

   making `α` and `a` **indices**, while every `@Eq.rec.{0,1} α a motive minor b h`
   application in the module assumes they are **parameters**. The in-tree kernel
   generates a recursor consistent with its own declaration form and accepts the
   module; Lean generates a different recursor and does not.

Repairing all three still fails: the elaborator reaches for `CoeFun` (absent
under `prelude`) trying to insert a coercion. **`lean file.lean` is elaboration,
codegen and parsing — not a kernel check.** Surface syntax makes the artifact
hostage to implicit-argument inference, universe unification, coercion insertion
and code generation, four systems that have nothing to do with whether the proof
term is well-typed.

## What this does and does not say

- It does **not** say the shell-bound mathematics is wrong. Three review passes
  found no error in the three theorems, and that stands.
- It does **not** say the term is ill-typed. That question is still open.
- It says the artifact has never been checked by anything except the kernel that
  produced it, and that the `0 sorry / 0 axiom` property was established by
  reading the text — `#print axioms` has never executed.

## The route

`axeyum-lean-import` already consumes official `lean4export` NDJSON **3.1.0**
fail-closed (`crates/axeyum-lean-import/src/lib.rs:1-11,51`). The export side
should be symmetric.

| id | item |
|---|---|
| **L1** | Emit `lean4export` 3.1.0 from `axeyum-lean-kernel`. The round-trip through our own importer is then a free differential test, and `leanchecker` (in the pinned toolchain) checks the terms. |
| **L2** | Restate `lean_pp.rs`'s doc comment to what it is — a human-inspectable rendering. **Done** in this change. |
| **L3** | Fix the three surface defects anyway, so the readable projection is also valid Lean. Cheap; makes the artifact openable in an editor. |
| **L4** | Put `lean` on the tooling `PATH` and gate the export through an external checker. A claim nothing checks will drift, and this one already did. |
| **L5** | Correct A2 and the paper's Lean paragraph: the toolchain is present, the export is rejected, the reason is architectural. |

Until L1 lands, the paper should say the module is emitted and inspected, and
should not imply that an independent kernel has accepted it.
