# ADR-0517: Lean has two checkers, and the kernel is the one we target

Status: accepted
Index-summary: `lean Module.lean` runs Lean's *elaborator*, whose reducer treats a `theorem` as opaque, while `Lean.Environment.addDeclCore` runs Lean's *kernel*, which unfolds it; the four `CReal` declarations Lean "rejected" are refused by the elaborator and accepted by the kernel, so the cross-check that carries the WHOLE carrier is the NDJSON kernel replay, and re-spelling every `theorem` as `def` makes the source route carry it too (measured, not taken here)
Index-status: accepted

Date: 2026-08-18

Related: [ADR-0511](adr-0511-the-shared-development-is-emitted-once-as-its-own-lean-module.md),
[ADR-0514](adr-0514-the-pinned-lean-toolchain-is-the-one-that-runs.md),
[ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md).

## Context

The strongest evidence this repository has is that official Lean reads our
exported bytes and accepts them. On 2026-08-18 the lane that rooted the shared
prelude module at the whole constructed-real carrier (ADR-0511) found that Lean
4.30.0 **refused** the emitted file:

```text
AxeyumCarrier.lean:792: error: Application type mismatch: …
  in the application AxNat.not_succ_le_zero AxNat.zero (And.rec …)   CReal.Equiv.not_zero_one
AxeyumCarrier.lean:828: error: Application type mismatch: …          CReal.not_le_one_zero
AxeyumCarrier.lean:881: error: (kernel) unknown constant …           (cascade)
```

The in-tree kernel admits all four. It had gone unnoticed because emission is
**reachability driven**: a refutation reaches only part of the carrier — 343 of
465 when that lane measured it — so the remaining 122 had never been handed to
any Lean at all. (This lane did not re-measure the reached count; it measured
the carrier, which is **470** today.)

Three explanations were possible and they are distinguishable:

1. our kernel is more permissive than Lean's — a soundness defect;
2. the renderer emits bytes that do not say what the checked term says;
3. a genuine incompatibility, which then has to be named and bounded.

## What was measured

**It is (3).** Lean has two entry points and only one of them is its kernel.

| route | what checks | verdict on the whole 470-declaration carrier |
| --- | --- | --- |
| `lean AxeyumCarrier.lean` | the **elaborator**, over surface syntax | 4 declarations refused |
| `lean --run scripts/lean/replay-lean4export.lean carrier.ndjson` | the **kernel**, `Environment.addDeclCore` from `mkEmptyEnvironment` | **all 470 accepted, 1.4 s** |

The kernel result is not a bare exit status: the replay reports
`environment now holds 470 constants`, and swapping
`CReal.Equiv.not_zero_one`'s proof for another closed proof makes the same
binary say

```text
REAL LEAN KERNEL REJECTED … but it is expected to have type
  Not (CReal.Equiv (CReal.ofRat Rat.zero) (CReal.ofRat Rat.one))
```

— so Lean's kernel demonstrably checked *that* declaration against *that* type.

### The mechanism, minimized to one token per line

Reproduced from the whole carrier module (2,541,928 B, 14.1 s, **exactly four**
declarations refused: `CReal.Equiv.not_zero_one`, `CReal.not_le_one_zero`, and
`CReal.not_equiv_mul_one_one_zero` / `CReal.no_total_inverse` as
`unknown constant` cascades) down to a 695,655 B module rooted at one
declaration (3.5 s), then to a one-line `example`, then out of `CReal`
entirely:

```lean
theorem probe_mod : Eq AxNat (AxNat.mod 4 2) 0 := Eq.refl (AxNat.mod 4 2)   -- ACCEPTED
theorem probe_gcd : Eq AxNat (AxNat.gcd 2 4) 2 := Eq.refl (AxNat.gcd 2 4)   -- REFUSED
```

**And then the decisive one.** Re-spell every `theorem` in the *same file* as
`def` — no other character changes — and Lean's elaborator accepts it:

| file | as emitted | every `theorem` re-spelled `def` |
| --- | --- | --- |
| `gcd 1 1 = 1` probe | refused | **accepted** |
| `CReal.Equiv.not_zero_one` module, 695,655 B | refused, 3.5 s | **accepted, 5.0 s** |
| whole carrier, 2,541,928 B, 470 declarations | 4 refused, 14.1 s | **accepted, 27.9 s** |

So the divergence is **the opacity of `theorem`**. Lean's `Meta.whnf` at default
transparency does not unfold a proof — proof irrelevance normally makes it
unnecessary — and Lean's kernel unfolds anything holding a value.

`Nat.gcd` is `WellFounded.fix` over the **definition** `Nat.lt_well_founded`,
and its Euclidean descent is justified by the **theorem** `Nat.mod_lt`. That is
exactly why the boundary falls where it does, measured case by case:

| reduction | recursion | elaborator |
| --- | --- | --- |
| `AxNat.mod 4 2 = 0`, `AxNat.div 4 2 = 2`, `AxNat.sub 4 2 = 2` | structural | accepted |
| `WellFounded.fix … lt_well_founded (fun _ _ => 7) 3 = 7` | one `Acc.rec` step, no theorem | accepted |
| `AxNat.gcd 0 3 = 3` | base case, no recursive step | accepted |
| `AxNat.gcd 1 1`, `1 3`, `2 2`, `2 3`, `2 4`, `3 6`, `4 6` | ≥ 1 recursive step, needs `mod_lt` | **REFUSED** |
| `Rat.num (Rat.natDivSucc 1 1) = Int.ofNat 1` | via `Rat.normalize` → `gcd` | **REFUSED** |

`mod` is the control that matters: it is the recursive step of the very
Euclidean descent `gcd` runs, equally closed and equally computational. The
second row rules out "`Acc.rec` does not reduce", which was the first and wrong
hypothesis here.

Two readings ruled out rather than assumed:

- **not the sharing pass.** The error reports the argument's type as a
  `let`-bound `_s7`, which invites a `zetaDelta` reading. Inlining every binding
  by hand reproduces the identical refusal. (`zetaDelta` is not a `set_option`
  name in 4.30.)
- **not a budget.** `maxRecDepth 1000000`, `maxHeartbeats 0` and
  `smartUnfolding false` each leave it unchanged, on the 7 MB file and on the
  two-line probe alike. `set_option diagnostics true` on the refused `gcd 1 1`
  shows the reducer unfolding `WellFounded.fix ↦ 2`, `Acc.rec ↦ 2`,
  `AxNat.gcd ↦ 2` and stopping — it does not run out, it gives up.
  `internal exception #3` is the command abort that follows the term error, not
  an independent failure; the two-line probe emits it too.

## Decision

**The kernel is the checker we target. The whole carrier goes to it, every
declaration, on every gate run; the `.lean` source route is a bounded residue
that is named and gated rather than silently reachability-limited.**

Concretely:

1. `real_lean_creal_carrier_kernel_replay` exports the **complete** checked
   environment (no reachability filter) and replays it through Lean's kernel.
   Its exit status depends on Lean's reported constant count **equalling** the
   count read out of our kernel, on the export still carrying the two residue
   declarations by name, and on a tampered proof for
   `CReal.Equiv.not_zero_one` being rejected with its own type named.
2. `real_lean_wellfounded_elaborator_divergence` states the incompatibility as
   a four-row table over the ℕ prelude alone — `mod` accepted, `gcd` refused,
   **the same gcd module with every `theorem` re-spelled `def` accepted**, and
   the kernel taking both — so the residue is a pinned, sub-second claim rather
   than a note about a 2.5 MB file, and the mechanism is isolated to one token
   per line. It fails if a future Lean closes the gap, and it also fails if the
   `def` spelling stops working, which would mean this ADR's account is wrong.
3. The shared prelude module (ADR-0511) stays rooted at the **reached union**,
   as that lane decided. Nothing here changes what a third party runs on a
   query module.

### What is deliberately NOT decided: the fix, measured and handed over

**Emitting proofs as `def` rather than `theorem` makes the source route carry
the whole carrier**, in 27.9 s, with no change to any term. That is a one-token
change in `lean_pp.rs` and it is *not* taken here, for reasons of blast radius
rather than doubt:

- it changes every artefact the repository ships, including the single-file
  front door that 18 real-Lean suites read;
- elaboration roughly doubles (3.5 → 5.0 s on one module, 14.1 → 27.9 s on the
  carrier) because the elaborator now unfolds proofs it used to skip;
- ADR-0458 has modules declare whether they contain reasoning, and "every proof
  is a `def`" is a claim about the artefact's character, not only its bytes.

`lean_pp.rs` is a file three lanes were in on 2026-08-18. The measurement above
is what a decision needs; the decision belongs to the lane that owns the
renderer, as its own ADR. A structurally recursive `Nat.gcd` would close the
same gap from the other end and is likewise deferred. Neither is required for
soundness: the kernel already accepts everything.

## Consequences

- The headline claim gets **stronger and better covered**, not weaker: what
  official Lean accepts went from a reachability-selected slice to **all 470**,
  and the checker is Lean's kernel rather than its elaborator.
- "Lean rejected our output" must always be qualified by *which Lean*. A
  refusal from `lean Module.lean` is an elaborator refusal until a kernel
  replay says otherwise, and a suite that does not say which entry point ran is
  not evidence — the same rule ADR-0514 applies to *which binary*.
- The residue of the SOURCE route is exactly: any declaration whose
  type-checking must reduce a `theorem`. Today that is `Nat.gcd`'s recursive
  step (justified by `Nat.mod_lt`), hence `Rat.normalize`, hence the four
  `CReal` declarations that discriminate by closed rational computation — two
  refusals and two `unknown constant` cascades, measured on the whole carrier.
  A fifth cannot appear unnoticed, because the carrier replay hands Lean every
  declaration rather than a reachable slice.

## Alternatives considered

- **Treat it as a renderer bug and keep patching the source route.** Rejected:
  the bytes are faithful, and the kernel replay proves it. Two days could have
  gone into `lean_pp.rs` for a defect that is not there.
- **Root the shared module at the whole environment anyway and exclude the four
  by name.** Rejected: an exclusion list is exactly the mechanism by which a
  fifth appears unnoticed, and it hides that the boundary is a *reduction*
  property rather than a set of names.
- **Declare the four unprovable / weaken them.** Rejected outright: they are
  the declarations that make `CReal.Equiv` and `CReal.le` non-total, i.e. the
  ones that stop the setoid witness being vacuous.

## Amendment 2026-09-03: the residue is keyword-independent

The "one token per line" row of `real_lean_wellfounded_elaborator_divergence`
(the gcd module with every `theorem` re-spelled `def`, expected *accepted*)
was written on 2026-08-18 from the CReal-carrier measurement and never ran
against a real binary in any gate until 2026-09-03. Run that day against both
Lean 4.30.0 (`d024af09`) and 4.34.0-rc1 (`3447a668`), the elaborator refuses
the `def` spelling with the same `Type mismatch` at the same `Eq.refl` as the
`theorem` spelling, while the kernel replay accepts the development. So the
mechanism named above — `Meta.whnf` treating a `theorem` as opaque — is not
what stops the source route: the elaborator's reducer does not take the
`WellFounded.fix` step through `Acc.rec` at default transparency whatever the
keyword, and the kernel does. The residue of the source route is therefore
*any declaration whose type-checking must reduce through `Acc.rec`*, which
is the same set as before (`Nat.gcd`'s recursive step, hence `Rat.normalize`,
hence the four `CReal` discriminators) stated without the keyword
qualification. The suite now pins the refusal of both spellings and fails if a
newer Lean accepts the `def` one. Every other conclusion of this ADR stands.
