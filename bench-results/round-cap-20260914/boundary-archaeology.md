# The pre-SAT skeleton envelope: what it is, where it came from, and whether it is calibrated

The brief asked for this before any change was proposed, because [ADR-2020] did
the same archaeology for a different constant and found `64` was *not* a unit
error but an uncalibrated proxy for an unbounded downstream solve, untouched
since June. **The answer here is different, and it is worth stating precisely
because the "115× headroom" framing invites the opposite conclusion.**

## The predicate

```rust
// crates/axeyum-solver/src/dpll_lia.rs
fn exceeds_pre_sat_skeleton_boundary(atoms: usize, cnf_vars: usize) -> bool {
    let crosses_base_trigger = atoms > 1_024 && cnf_vars > 4_096;
    let (envelope_atoms, envelope_cnf_vars) = moderate_pre_sat_envelope();  // 10_240 / 16_384
    crosses_base_trigger && (atoms > envelope_atoms || cnf_vars > envelope_cnf_vars)
}
```

Two constants, not one. The **base trigger** refuses nothing on its own; the
**moderate envelope** is what decides admission.

## It has been revisited twice, the second time six days ago

`git log -S MAX_MODERATE_PRE_SAT_ARITH_ATOMS -- crates/axeyum-solver/src/dpll_lia.rs`
returns exactly two commits.

| commit | date | envelope | what it was for |
|---|---|---|---|
| `8a6de50ac` | **2026-08-10** | introduced at **1,280 / 8,192** | `fix(arith): restore bounded LRA monotonicity` |
| `832c2afd0` | **2026-09-08** | raised to **10,240 / 16,384** | `fix(lia): re-derive the pre-SAT rectangle against the engine that actually runs` |

So this is **not** the `64` case. It is not a forgotten number, and its current
value was set by a documented, controlled measurement six days before this lane.

## But its ORIGIN is not a memory bound, and its STATED justification is refuted

**2026-08-10 — the envelope is a fitted exception, not a derived bound.** Its
[preregistration](../../docs/plan/qf-linear-a5-pre-sat-boundary-monotonicity-v1-preregistration-2026-08-10.md)
and [result](../../docs/plan/qf-linear-a5-pre-sat-boundary-monotonicity-v1-result-2026-08-10.md)
say what it was for in their own words: a query
(`QF_LRA/sal/windowreal/windowreal-no_t_deadlock-17.smt2`) had gone from
historical UNSAT to a typed resource `unknown`, and the rectangle was carved to
admit it back while two named **abort controls** (`pursuit-safety-16`,
`tgc_io-safe-20`) kept declining. It *repairs one deterministic historical
loss*; it is explicitly "not an A5 score gain". The shape of the region is
whatever separated one file it wanted from two it did not.

**2026-09-08 — the re-derivation refutes the memory story it inherited.** Its own
doc comment measures peak RSS at **71.3 MiB** on the largest admitted point
(9,846 atoms / 12,155 CNF vars) against the **8 GiB** ceiling the bound cites —
**1/115th** — with peak RSS moving by at most **0.5 %** whether the envelope was
enforced or removed, and records that *"there is no measured memory risk anywhere
in the region it was refusing."* It also kills the bound's own named control:
`pursuit-safety-16` is `QF_LRA`, does **not** reach this gate through the shipped
front door, and peaks at 3.47 GiB identically either way — *"the bound does not
protect the case it names."* It then set the envelope to the largest point
measured safe and said plainly: *"above this, nobody has measured, and unmeasured
is not the same as safe."*

## Somebody has now measured above it, and it is worth zero

That sentence is the one the brief's "115× headroom" reading rests on, and it is
**no longer true**. [ADR-2020] raised the envelope **4×** behind
`AXEYUM_GROUND_DECIDE_PRESAT_ENVELOPE` and measured the shipped 129-file
population: **0 of 129 moved**, Wilson `[0.0 %, 2.9 %]`, at 1.00× wall, with the
null shown non-vacuous and the refusal measured **converting into a timeout**.

## Verdict: correct as set, for a reason its documentation does not give

1. **It is not an uncalibrated leftover.** Both of its values came from a
   controlled measurement with a written method, the second six days ago.
2. **It is not doing the job it says it is doing.** As a *memory* bound it has
   two orders of magnitude of headroom and its own re-derivation says its named
   control is not protected by it.
3. **It is, empirically, in roughly the right place as a TIME proxy** — which is
   a job nobody calibrated it for. Removing it 4× does not decide anything; it
   converts a fast refusal into a slow timeout. On this population the skeleton
   is not merely inadmissible, it is undecidable inside the budget.
4. **Do not raise it again.** The 115× figure is a memory number and the bound is
   not binding for memory reasons. Raising it has been measured and is worth
   zero. [ADR-2020]'s own redirect is the live one: *the target is the SIZE of
   the set, not the bound that refuses it.*

## Two quotations that get mixed up, and must not be

The 2026-09-08 re-derivation reports **"3 of the 10 refusals are decided when the
envelope is removed"**; [ADR-2020] reports **0 of 129**. These do not conflict
and neither transfers to the other: the first is `QF_LIA` reference-only loss
files, the second is the `UFLIA`/`UFNIA` ground-decide population. Quoting
either without its population is how a refuted number stays in circulation.

## What is still owed, in the constant's own words

> A rectangle in (atoms, CNF vars) is the wrong shape for a memory bound at all
> — [ADR-1752] already replaced exactly this pattern in `lra_online`
> (`MAX_ONLINE_LRA_ATOMS`, a flat atom cap) with a byte budget and measured
> per-atom costs. Doing the same here is the real fix and needs an ADR.

That remains open, and this lane does not do it: a byte budget would move the
boundary's *shape*, and the measured fact is that its *position* is not what
costs us these files.
