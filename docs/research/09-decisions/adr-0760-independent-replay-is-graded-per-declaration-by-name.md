# ADR-0760: Independent replay is graded per declaration, by name

Status: accepted
Date: 2026-08-30
Index-summary: S4 of ADR-0717. A replay grade is membership of a declaration's
own name in the set of constants pinned Lean's kernel ended holding, read from
`env.constants`; a carrier-wide COUNT confers nothing on any member. Measured
on the whole `creal` carrier: population 2,045, representable 1,972,
`checked=1972 expected=1972 missing=0 extra=0`. Two findings: this kernel
admits 48 `Theorem`s whose type is not a `Prop` (Lean's kernel refuses them,
25 more blocked by depending on one), and the registered whole-carrier replay
gate was SIGABRTing on a stack overflow before a single Lean ran.

Phase: S4 of the trusted-library safety roadmap (ADR-0717)
Lane: `l0-s4-independent-replay`

## Context

ADR-0717's threat model puts **kernel unsoundness first**: our own kernel
accepting an invalid term. Every other protection in the fact ledger assumes
our kernel is right. S4 is the only phase that does not, and S0's safety matrix
measured it as the thinnest protection of all nine —
`independent_replay` at **8 / 2117** proved facts, and **0 / 20** across the
IVT/EVT rows that carry the programme's loudest claims.

That 8 is what facts *claim*. `scripts/gen-safety-matrix.py` decides the column
by matching `checker_command` text against a regex; it executes nothing.

The instrument to measure instead already existed.
`scripts/lean/replay-lean4export.lean` drives `Lean.Environment.addDeclCore`
from our official `lean4export` NDJSON — Lean's **kernel**, starting from
`mkEmptyEnvironment`, with no elaborator, no implicit-argument insertion and no
code generator. `real_lean_creal_carrier_kernel_replay` already pointed it at
the whole constructed-real carrier.

## The problem with what existed

That suite asserts pinned Lean ends with **the same NUMBER of constants** this
kernel holds. That is a strong statement about the carrier and a weak one about
any theorem in it. `environment now holds N constants` is consistent with a
stream in which the declaration a reader cares about was renamed, substituted,
or absent while some other declaration made up the total.

So no individual fact could honestly cite it. Citing it would grade a theorem
from its family's aggregate, which is precisely the inheritance S4's exit
clause forbids: *no accepted theorem receives a stronger grade by inheritance
from a sampled family.*

## Decision

**A declaration's independent-replay grade is membership of its own name in the
set of constant names Lean's own kernel ended holding.** Nothing else confers
it.

1. `replay-lean4export.lean` gains `--emit-names <out>`, writing the sorted
   names of `env.constants`. That is **Lean's environment, not our stream**, so
   a name in it was *admitted* by Lean's kernel rather than merely transmitted
   by us.
2. `grade(subject, admitted)` is an exact set membership test. It consults no
   family, module, prefix, or sibling. A function that grades a family by
   sampling does not exist and must not be added.
3. Axeyum acceptance and Lean acceptance stay **separate grades**. A
   declaration this kernel admitted and Lean has not seen reads
   `axeyum=accepted lean=not-replayed`, never as though Lean saw it.
4. Every declaration Lean cannot be given carries a **typed reason**, and the
   reason must be *earned* against Lean, not asserted by us.
5. The census population is read from `kernel.environment()`. An "every X" test
   that iterates its own list measures the maintainer's memory.

## What the measurement found

One run, pinned Lean 4.30.0 (`d024af09`), whole `creal` carrier:

    population=2045 representable=1972
      theorem_type_not_prop=48 blocked_by_dependency=25
    checked=1972 expected=1972 missing=0 extra=0

### Finding 1 — this kernel admits `Theorem`s whose type is not a proposition

Lean's kernel refuses them:

    REAL LEAN KERNEL REJECTED the declaration:
      (kernel) type of theorem 'CReal.weierstrassMTest' is not a proposition

48 declarations are in this class, and 25 more are blocked by depending on one.
They are **deliberate and the reason is sound**:
`creal/uniform_convergence.rs` makes `CReal.UniformConvergesOn` `Type`-valued
because the convergence *rate* must be data — `Exists.rec` cannot eliminate
into `Type`, so an `∃ rate, …` cannot be used to build the `Nat → Nat` modulus
a later construction needs. `CReal.UniformlyContinuousOn` and
`CReal.HasDerivativeOn` are `Type`-valued for the same reason, which is why
the derivative family dominates the list.

What was missing is that nothing recorded these as outside what Lean will
accept **as a theorem**. Lean would take each as a `def`; it will not take any
as a `theorem`. This is a measured disagreement between two kernels about what
may be called a theorem, not a wire-format limitation and not an export defect.

It is not a demonstrated soundness hole, and this ADR does not claim one. It is
a real gap in independent checkability, sitting in exactly the place ADR-0717
says to look.

### Finding 2 — the whole-carrier replay gate could not reach a verdict

`real_lean_creal_carrier_kernel_replay` is registered in
`scripts/check-lean-gate.sh` and was **SIGABRTing on a stack overflow before a
single Lean ran**: `creal` needs 16 MiB in debug
(`artifacts/kernel-stack-envelope.tsv`) and a `#[test]` thread has 2 MiB.
Measured in a shell with `RUST_MIN_STACK` unset, so this is not one-shell
contamination.

Wrapped in `on_a_deep_stack`, it now reaches Lean — and fails on Finding 1,
because its claim is over the *whole* carrier and 73 declarations cannot be
handed to Lean's kernel as theorems. **So the claim
`F:lean-kernel-accepts-the-whole-constructed-real-carrier` makes is not
currently re-derivable.** This lane does not edit facts; the finding is
reported for the fact's owner.

## Consequences

- `real_lean_replay_census` is the gating artifact, at a monotone floor of
  1,900 (72 below the measurement). Registered in `check-lean-gate.sh`, whose
  counted floor moves 223 → 229 for six real-Lean invocations.
- A fact may cite this census for a subject **only** when the run prints
  `grade subject=<name> … lean=replayed` for that name. A sibling's line
  confers nothing.
- The 73 non-representable declarations keep Axeyum-only labeling and a typed
  reason. Closing that gap means deciding whether the `Type`-valued carriers
  should be exported as `def`s so Lean can check them at all — a separate
  decision, and the natural S4 follow-on.

## Alternatives rejected

- **Cite the carrier count per fact.** This is the inheritance the exit clause
  forbids, and Finding 1 shows the count claim is false anyway.
- **Exclude the non-representable declarations silently.** A classifier that
  can exclude anything it likes and stay green is the checker-that-cannot-fail
  defect. The exclusion is earned: the suite hands Lean the excluded
  declaration and requires the refusal to come from the kernel, to say "is not
  a proposition", and to name the subject.
- **Per-subject root-closure replay for all 2,045.** Correct but slow; the
  representable-slice export gives the same per-name evidence in one Lean
  invocation. Root-closure replay is still used where a *narrow* environment is
  the point — the inheritance guard depends on it.

## Controls

Four mutations, kill sets measured, **including the survivor**:

| mutation | tests killed |
|---|---|
| `grade` prefix-matches instead of exact | 1 — the pure guard only |
| `grade` always returns `Replayed` | 2 — both inheritance guards |
| `is_a_proposition` always `true` | 2 — census + earned typed reason |
| Lean reports zero constant names | 3 — every Lean-dependent test |

The first mutation **survived** the Lean-attested inheritance guard, and that is
worth recording rather than hiding: `CReal.ivt_approx` is not a prefix of
anything in `CReal.ivt_step`'s 359-constant closure, so prefix matching is
invisible end to end and only the pure guard catches it. The two guards are not
redundant — they fail on disjoint defects, which is why both are kept.
