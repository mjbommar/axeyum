# ADR-0581: The kernel's stack envelope is measured, not limited

Status: accepted
Date: 2026-08-26
Index-summary: Kernel recursion gets a measured stack budget and a ratchet, not a recursion-depth limit

## Context

The in-tree Lean kernel's type checker is directly recursive over the term —
`infer_core` → `infer_app`/`infer_lambda` → `check_core` → `infer_core`, with
`whnf_core`, `def_eq_core_uncached`, `instantiate_aux` and `abstract_aux`
recursing alongside it. That is the same design Lean's own kernel has, and
depth proportional to term depth is not a flaw in it.

It has no bound of any kind. `KernelError`'s own doc comment says "All variants
are returned, never panicked: the kernel rejects malformed or out-of-scope input
deterministically", and of its ~55 variants exactly one is an exhaustion variant
(`NestedInductiveExpansionLimit`, ADR-0355). Stack exhaustion is outside that
contract entirely: the process **aborts**. `fatal runtime error: stack
overflow`, SIGABRT, exit 134, nothing catchable, nothing reported.

That symptom is indistinguishable from a broken tool or an absent declaration,
and this repository has read it as both — an agent reported
`prelude_theorem_inventory` as broken when it had only omitted `--release`, and
`scripts/check-fact-depends-derived.py` could not validate ANY kernel-route
fact's `depends_on` for as long as it ran the debug form. It became urgent on
2026-08-26 when `CReal.e` landed and
`every_creal_declaration_is_checked_and_axiom_free` — the single test standing
behind this project's axiom-freedom claim — began aborting instead of running.

The state of the practice was eight verbatim copies of a thread-spawning helper
at three sizes (64 MiB ×5, 256 MiB ×3, 1 GiB ×1), no shared constant, and no
measurement behind any of the numbers. Nothing anywhere asserted the property
"the kernel can check what it admitted."

There is no prior ADR on the resource envelope. ADR-0536 touches it only to
record that a stack overflow on `2^64`-scale literals is a *deliberate* negative
signal for the lazy-delta acceleration site, and to reject adding a probe
counter to `Kernel` ("no new field on the trusted kernel").

## Decision

**The kernel's stack requirement is a measured, pinned, gated number. The kernel
gets no recursion-depth limit and no new refusal.**

Concretely:

- One constant, `axeyum_lean_kernel::DEEP_STACK_BYTES` = 256 MiB, and one
  helper, `on_a_deep_stack`, replace every hand-rolled copy.
- `examples/kernel_stack_envelope` builds one prelude on a thread of an exact,
  caller-given size and reports the answer as its **exit status** — 0, 134, or 2
  for a usage error. It must be a separate process because an overflow aborts
  the one that suffers it.
- `artifacts/kernel-stack-envelope.tsv` pins the requirement per
  (profile, prelude), and `scripts/check-kernel-stack-envelope.sh` re-derives it
  by bisection. Growth turns the gate red **with the number and the word
  "stack" in it**, instead of aborting mysteriously.
- Nothing in `crates/axeyum-lean-kernel/src/` changed. No new field on `Kernel`,
  no new `KernelError` variant, no new way for the checker to say no.

## Evidence

### The requirement, measured

Smallest power-of-two thread stack on which each prelude's build completes,
found by bisection (2026-08-26, s4). One power of two lower, the process aborts.

| prelude   | debug          | release   | ratio |
|-----------|---------------:|----------:|------:|
| `cpoint`  | **33,554,432** | 1,048,576 |   32× |
| `complex` |      4,194,304 |   262,144 |   16× |
| `creal`   |  **2,097,152** |   131,072 |   16× |
| `rat`     |      1,048,576 |   131,072 |    8× |
| `nat`     |        262,144 |    65,536 |    4× |
| `integer` |        262,144 |    65,536 |    4× |
| `logic`   |        131,072 |   < 8,192 |  >16× |

Three findings:

1. **`creal` in a debug build needs exactly 2,097,152 bytes — exactly the
   default stack a spawned thread gets, which is what a `#[test]` runs on.**
   There was never any margin. One deep declaration was always going to end it,
   and one did.
2. **`cpoint` in a debug build needs 32 MiB**, so the five sites that used a
   64 MiB helper had **2×** headroom, not the comfortable margin the number
   looks like.
3. **Debug costs up to 32× release for the same term at identical recursion
   depth.** That is the measured reason `prelude_theorem_inventory` must be run
   `--release`.

### Where the depth comes from

Instrumenting `infer_core`, `whnf_core`, `def_eq_core_uncached` and
`instantiate_aux` with a stack-pointer probe, at the deepest sampled point of a
`creal` build the chain was 41 × `infer_core`, 34 × `check_core`, 26 ×
`infer_app`, 15 × `infer_lambda`, 8 × `instantiate_aux`. The `infer_core` →
`infer_core` edge cost ~1,900–2,250 B per level in debug; `instantiate_aux`
~576 B. By raw depth `instantiate_aux` dominates (1,197 nested frames for
`cpoint`); by stack it is the type-checker cycle. Neither is a defect: it is
what recursive checking of a large term costs.

`Kernel::axiom_footprint` is **not** implicated — it and `collect_const_deps`
are explicit worklists. The doc comment on the 1 GiB patch in
`creal/creal_tests.rs` attributes the overflow to the footprint walk; the cost
is in `built()`, the environment build.

### The instrumented number was wrong, and in the believable direction

That probe reported a `cpoint` peak of 1,681,616 B — **12× below the bisected
33,554,432 B**. A probe sees only the frames it is installed in, and the deepest
recursion of a run need not pass through any of them (`Kernel::abstract_aux`
recurses over the term and was not instrumented). The first draft of this work
took the small number as the answer and would have set the shared constant from
it. Recorded here because the failure is generic: **an in-process probe measures
a chosen subset; a subprocess bisection measures the process.**

### Lean 4's own kernel

Read from the pinned toolchain on this host (exported symbols and disassembly of
`libleanshared.so`, plus `Lean/Environment.lean`, `Lean/Util/RecDepth.lean`):

- Lean **4.30**, the version this repository pins, guards kernel recursion with
  a **stack-pointer probe**, not a depth counter: `check_system("type checker")`
  → `check_stack` compares the current frame against a cached stack base with a
  **128 KiB safety margin** and throws a catchable `lean::stack_space_exception`.
- That surfaces as a first-class error value, not a crash:
  `Kernel.Exception` has `deterministicTimeout | excessiveMemory |
  deepRecursion | interrupted` alongside the type errors, and `addDeclCore`
  returns `Except Exception Environment`.
- `maxRecDepth` is an **elaborator** option. In 4.30 it never reaches the
  kernel at all. Lean **4.34** adds `scope_rec_depth`, a TLS depth counter
  (limit scaled ×16), forwarded into `addDeclCore` — **in addition to** the
  SP probe, funnelling into the same exception.

So the closest thing to prior art uses a stack probe first and a counter only as
a later supplement.

### The gate can fail

`scripts/tests/test-kernel-stack-envelope.sh` carries six controls. Mutating
each of the checker's five guards in a scratch tree kills **exactly one**
control, and the one that names it:

| guard removed | control that dies |
|---|---|
| the "observed failure" requirement | budget that cannot fail WARNs |
| the exit-2 usage-error discrimination | probe usage error is exit 2 |
| the empty-ledger guard | no matching rows is RED |
| the missing-pin-file guard | missing pin file is RED |
| the over-budget failure | budget below requirement is RED |

The first mutation run reported all six controls dying for every mutant — the
scratch tree was not a cargo workspace, so every mutant "died" at cargo's exit
101 and the harness reported total coverage while measuring nothing.

## Alternatives

### Rejected: a recursion-depth counter in `tc.rs` returning `KernelError::RecursionLimit`

This was the proposal that prompted the investigation, and the measurements
refute it on four independent grounds:

1. **Depth does not predict stack.** The two deep recursions here cost ~2,250 B
   and ~576 B per frame — a 4× spread — and which one dominates depends on the
   term. A depth number is not the quantity that runs out.
2. **A single constant cannot serve both profiles.** Debug frames cost up to
   32× release frames at *identical* depth. A limit safe in debug rejects terms
   release handles comfortably; one tuned for release does not fire in debug.
3. **It would guard the wrong functions.** Only `infer_core`/`check_core` return
   `Result`. `whnf_core` returns `ExprId`, `def_eq_core` returns `bool`,
   `instantiate_aux` and `abstract_aux` return `ExprId`. A limit that only
   `infer_core` can report leaves the paths that actually recurse deepest
   unguarded — and `abstract_aux`, which the probe missed entirely, is one of
   them.
4. **Early return from a substitution is not obviously fail-closed.**
   `instantiate_aux` returning its input unsubstituted yields a term with loose
   `BVar`s. `LooseBVar` is a refusal, so the likely outcome is safe — but
   "likely safe" is the wrong standard for the trusted kernel, and establishing
   it properly is a soundness argument, not a bounds check.

Beyond the mechanics: a depth limit is **a new way for the checker to say no**,
and this repository's standing rule is that a refusal must never be confusable
with a proof. Adding one to fix a *tooling* problem — a guard that stopped
running — is disproportionate. The abort is not a soundness event; it is a
resource limit wearing a crash's clothes, and what was actually broken is that
nothing measured it.

### Deferred, not rejected: a stack-headroom probe in the kernel

The right shape, when it is wanted, is Lean 4.30's: an
`ensure_stack_headroom()` check at the same call sites Lean uses, returning a
`KernelError::DeepRecursion` that is `Except`-shaped and catchable, so a caller
can *report* exhaustion instead of dying of it. It adapts to the profile for
free, which a depth counter cannot.

It is deferred because it needs three things this ADR does not have: a design
for reporting exhaustion out of the four functions that cannot return `Result`;
an argument that under-reduction and forced `def_eq` failure are refusal-
monotone at every call site; and a decision on carrying state on `Kernel`, which
ADR-0536 declined for a statistics probe and which a resource limit deserves to
be argued separately. Its **value** is also bounded: it converts an abort into
an error, and the pinned envelope already converts it into a gate failure with a
diagnostic. Do it when a caller genuinely needs to survive exhaustion — a
long-running service checking untrusted terms — not to make a test suite green.

### Rejected: `RUST_MIN_STACK`

A test that passes only under an ambient environment variable is a gate on one
shell. Already measured here: a lane had it exported from an earlier
hand-bisect, reported a suite green, and the same test aborted in a clean shell.
The size is an explicit argument everywhere in this design for that reason.

### Rejected: an in-process peak-stack probe as the gate's measurement

Stack painting needs `unsafe`, denied workspace-wide. An instrumented
low-water-mark probe is what under-measured by 12×. The bisection has no such
blind spot and needs no kernel change.

## Consequences

**Easier.** One number to change and one place to change it. Growth of the
library produces a red gate naming the stack and the prelude, with a
`--measure` command that re-derives the row — instead of an abort that three
separate readers have mistaken for a broken tool. Every green run of the gate
has demonstrated, on that run, that it can go red.

**Harder.** The gate costs real time: a debug `cpoint` probe is ~63 s against
~8 s for release, so `--profile debug --prelude cpoint` is ~2 minutes. The
release profile is the cheap smoke version and the debug rows are the ones that
match where `cargo test` actually runs.

**Revisit when.** (a) A caller needs to survive stack exhaustion rather than
gate against it — then implement the deferred headroom probe. (b) The `cpoint`
debug row approaches `DEEP_STACK_BYTES`; at 32 MiB against 256 MiB there is 8×,
and the 64 MiB sites were at 2× before anyone measured. (c) `creal/integral.rs`'s
concrete-instantiation tests get a measured floor — they are the workload that
set the constant and the only one still unmeasured.

**Left undone deliberately.** `crates/axeyum-lean-kernel/src/creal/creal_tests.rs`
still carries a private 1 GiB `on_a_deep_stack_creal`; another lane owns that
file. It should become `on_a_deep_stack`, and its doc comment should stop
attributing the overflow to the `axiom_footprint` walk, which is an explicit
worklist and cannot recurse.
