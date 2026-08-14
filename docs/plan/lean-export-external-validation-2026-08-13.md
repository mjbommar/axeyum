# Lean external validation — measurement, defect and resolution, 2026-08-13

**Read the last section first if you want the outcome.** The Lean export was
rejected by real Lean in the morning and is accepted by Lean's own kernel by the
evening; every defect was in the pretty-printer. This document keeps the whole
sequence, in order, because two of the wrong turns were mine and the reasoning
that produced them is more reusable than the fix.

Closes the open question behind item A2 of
[next actions from the Rado paper](next-actions-from-the-rado-paper-2026-08-12.md),
which read:

> One command on any host with a toolchain converts *"we emitted a Lean module"*
> into *"an independent kernel accepted it."* Very high credibility per unit of
> effort, and it is the single cheapest item on this list.

The command was run and the answer was negative. The premise — that one command
would settle it — was wrong; the eventual route was an export format and a
kernel replay. Full reproduction of the original measurement:
`/nas3/data/axeyum/frontier-2026-08-13/coordinator/logs/lean-export-check-2026-08-13.md`.

> **Superseded in place:** the sections below say "is rejected", "has never
> executed", and "surface syntax is hostage to the elaborator". All three were
> true when written and are false now. The corrections are at the end rather
> than edited in, so the sequence stays legible.

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

## The guard that was supposed to prevent this was never implemented

Found after the above, and it is the more important defect.

`lean_pp.rs:214-216` documents a **defensive guard**:

> Only **non-parametric, non-indexed** inductives (enums / flat datatype
> families) are emitted as real `inductive`s; a listed inductive that is
> parametric or indexed falls back to the axiom rendering (a defensive guard —
> the is-tester families are always flat).

`Eq` is parametric *and* indexed. Under that guard it would have been rendered
as an `axiom`, and this failure could not have occurred.

`render_real_inductive` (`lean_pp.rs:409-441`) opens with a matching comment —
"Only flat (no params, no indices) inductives" — and then performs **no
flatness test at all**. It fetches the `Declaration::Inductive`, writes
`inductive {name}{uparams} : {render_lean(ty)} where`, appends the
constructors, and returns. Its only two `None` paths are "not an `Inductive`"
and "a listed constructor name is not a `Constructor`"; neither concerns
parameters or indices.

The guard is not bypassed and its test is not wrong. **It was never written.**
It exists only in prose, in two places, describing behaviour the code does not
have — the failure mode CLAUDE.md's "Gotchas" section is entirely about.

### The corpus is structurally incapable of reaching the defect

The real-Lean cross-check fixtures build their inductives as
`add_inductive(two, &[], 0, prop, ...)`: zero parameters, zero indices, a flat
two-constructor enum — precisely the shape a *working* guard would admit. No
amount of running the existing suites could have found this.

**And it was predicted in writing.** `docs/prover-track/research/06-kernel-gap-analysis.md`,
item 7 of "what must be true before a goal layer can sit on this kernel",
states that widening the corpus requires `lean_pp` to stop falling back to
axiom rendering for parametric/indexed families, "otherwise widening the corpus
silently widens the *vacuous* region." That is now a realised prediction rather
than a hypothetical.

It is also the strongest argument for the `lean4export` route over patching the
source printer: **the wire format carries `numParams` natively and structurally
cannot flatten the telescope**, whereas a source printer can always regress into
doing so — and, as this shows, can do it while carrying a comment saying it does
not.

Confirmed from the kernel side: `prelude.rs:321-322` declares `Eq` correctly and
says so verbatim ("`Eq.{u} {α : Sort u} (a : α) : α → Prop` ... 2 params (α, a),
1 index, one ctor"). The kernel holds the right shape; the printer discards it.

## Stating the Lean position without overstating either direction

Both halves of the obvious summary are wrong, in opposite directions.

- **Not** "Lean → axeyum works." It is five pinned single-root fixtures,
  dual-admitted against official v4.30. L3 is 0/12, the String closure's first
  blocker is unmeasured, and the parity contract itself says the 5/5 fixture
  total "is not complete K1 authority." Accurate: *translates and independently
  admits a measured five-root fixture profile; the dependency-closed
  Init/Std/mathlib population is unstarted.*
- **Not** "axeyum → Lean does not exist." `lean_pp.rs` is 1,690 lines and four
  suites feed rendered modules to a real Lean binary. Accurate, sharper, and
  less flattering: **an export path exists, and the only non-trivial artifact
  ever put through official Lean is rejected.**

"Does not exist" invites "so build it". "Exists and is rejected" is the true
state, and it is the one that should reach the paper.

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

## Resolved the same day — and my architectural conclusion was wrong

Everything above stands as a record of the defect. **The conclusion I drew from
it does not.**

I wrote that repairing the three known defects "still fails, because the
elaborator reaches for `CoeFun`", and inferred that surface syntax is
structurally hostage to elaboration — that `lean file.lean` could not be a
route because implicit-argument inference, universe unification and coercion
insertion stand between the artifact and the kernel. That inference was too
strong, and it was drawn from a single unexplained error message.

**There was a fourth printer defect, not an architectural limit.** Lean inserts
a constant's pending implicit arguments as soon as a *parenthesized*
application is complete, so `(@Eq.refl α) a` fails where the flat
`@Eq.refl α a` checks. The writer emitted nested spines `((f a) b)`. Both
engines now print flat spines. With that repaired:

```
$ lean shell_closed_form.lean
EXIT=0, 0.138 s
'shell_closed_form' does not depend on any axioms
```

`#print axioms` has now executed for the first time. Non-vacuity is measured,
not assumed: mutating the theorem *statement* gives `EXIT=1`, "Type mismatch".

**And independent kernel acceptance was two API calls away, not a research
project.** `import Lean` works from a bare `lean --run` on the pinned
toolchain; `mkEmptyEnvironment` + `Environment.addDeclCore` are the entire
requirement. `scripts/lean/replay-lean4export.lean` feeds our NDJSON to Lean's
own kernel — no elaboration, no codegen, no `lean4export` install, no
third-party checker, starting from an **empty** environment so nothing is
satisfied by Lean's `Init` and the `Quot` double-add trap cannot arise. All 17
official v4.30 fixtures are accepted, and so is the axeyum Rado development
(3,854 records, 74 declarations, 97 constants). The negative control is a gate:
given another theorem's closed well-typed proof, Lean's kernel restates *our*
theorem and refuses it. Verified independently by the coordinator:
`cargo test -p axeyum-lean-kernel --test real_lean_kernel_replay` → 1 passed.

### The correction that matters more than the fix

Three times in one day I turned a real measurement into a claim about a
capability, and was wrong each time:

| I wrote | actually |
|---|---|
| "the toolchain is absent (verified)" (inherited, repeated) | installed and pinned; `which` measured `PATH` |
| "axeyum → Lean does not exist / is broken" | 163 modules across 70 families already cross-checked |
| "surface syntax is hostage to the elaborator" | a fourth printer bug; flat spines fixed it |

The evidence was sound every time; the generalisation was not. The pattern is
specific enough to guard against: **an unexplained failure is evidence about
one artifact, and becomes evidence about a capability only when its mechanism
is understood.** `CoeFun` was a symptom I could not explain, and I promoted it
to a law.

What survives unchanged: `lean file.lean` *is* elaboration and codegen rather
than a kernel check, so the NDJSON route remains the right one for
trust — but that is an argument about what the artifact proves, not about
what is achievable.
