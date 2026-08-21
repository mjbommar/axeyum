# Lane notes: `agent-creal-lean-divergence` — which Lean rejected it

The handover said: **our kernel admits four declarations that Lean's kernel
rejects.** It does not. Lean's kernel accepts all 470 declarations of the
constructed-real carrier, in 1.4 seconds, including the four. What refuses them
is Lean's **elaborator**, and the two are not the same checker.

## 1. Reproduce it minimally

| step | artefact | elaborator |
| --- | --- | --- |
| whole carrier (sharing on) | 2,541,928 B, 470 declarations | 4 refused, 14.1 s |
| module rooted at `CReal.Equiv.not_zero_one` alone | 695,655 B, 257 declarations | refused, 3.5 s |
| one `example (h : <the Rat.le prop>) : AxNat.le 1 0 := h` in that context | — | refused |
| two `theorem`s over the **ℕ prelude only** | see below | one refused |

The four on the whole carrier are exactly `CReal.Equiv.not_zero_one` and
`CReal.not_le_one_zero`, plus `CReal.not_equiv_mul_one_one_zero` and
`CReal.no_total_inverse` as `(kernel) unknown constant` cascades. The
handover's "plus two theorems citing the first" is right.

```lean
theorem probe_mod : Eq AxNat (AxNat.mod 4 2) 0 := Eq.refl (AxNat.mod 4 2)   -- ACCEPTED
theorem probe_gcd : Eq AxNat (AxNat.gcd 2 4) 2 := Eq.refl (AxNat.gcd 2 4)   -- REFUSED
```

`internal exception #3` is not a diagnosis and is not a second failure: it is
the command abort that follows a term error at a `theorem`. The two-line probe
above emits it too.

## 2. Which of the three it is, and how I know

`scripts/lean/replay-lean4export.lean` drives `Lean.Environment.addDeclCore`
from our official `lean4export` NDJSON — Lean's kernel, from
`mkEmptyEnvironment`, no elaborator anywhere. Over the **whole** carrier:

```text
lean4export replay: the real Lean kernel accepted 438 declaration records
  (14 inductive groups, 14 also compared field-by-field over 46 constants),
  environment now holds 470 constants                              1.4 s
```

That is not an exit status. Swapping `CReal.Equiv.not_zero_one`'s `"value"` for
another closed proof makes the same binary say

```text
REAL LEAN KERNEL REJECTED … but it is expected to have type
  Not (CReal.Equiv (CReal.ofRat Rat.zero) (CReal.ofRat Rat.one))
```

so Lean's kernel checked *that* declaration against *that* type. Explanation (1)
— our kernel more permissive — is **refuted**; so is (2), since the bytes Lean's
kernel read are the ones the renderer produced. It is (3), and the boundary is
sharp:

**Lean's elaborator does not unfold a `theorem` while reducing; its kernel
does.** The decisive measurement is a one-token rewrite of the *same file*,
`theorem` → `def`, nothing else changed:

| file | as emitted | every `theorem` re-spelled `def` |
| --- | --- | --- |
| `gcd 1 1 = 1` probe | refused | **accepted** |
| `not_zero_one` module, 695,655 B | refused, 3.5 s | **accepted, 5.0 s** |
| whole carrier, 2,541,928 B, 470 decls | 4 refused, 14.1 s | **accepted, 27.9 s** |

`Nat.gcd` is `WellFounded.fix` over the **definition** `Nat.lt_well_founded`,
and its Euclidean descent is justified by the **theorem** `Nat.mod_lt`. That is
why the boundary falls exactly here:

| reduction | recursion | elaborator |
| --- | --- | --- |
| `AxNat.mod 4 2 = 0`, `div 4 2 = 2`, `sub 4 2 = 2` | structural | accepted |
| `WellFounded.fix … lt_well_founded (fun _ _ => 7) 3 = 7` | one `Acc.rec` step, no theorem | accepted |
| `AxNat.gcd 0 3 = 3` | base case, no recursive step | accepted |
| `gcd 1 1`, `1 3`, `2 2`, `2 3`, `2 4`, `3 6`, `4 6` | ≥1 step, needs `mod_lt` | **REFUSED** |
| `Rat.num (Rat.natDivSucc 1 1) = Int.ofNat 1` | via `Rat.normalize` → `gcd` | **REFUSED** |

My first hypothesis — "`Meta.whnf` refuses `Acc.rec`" — is **wrong**, and rows 2
and 3 are what killed it. `mod` is the control that matters: it is the recursive
step of the very Euclidean descent `gcd` runs.

**Does the rejection depend on the proof or on the statement?** Neither: on
whether *checking* the term must reduce a `theorem`. The statement elaborates
fine — Lean prints it back in the error. The proof of `not_zero_one` closes a
closed `Rat.le` down to `Nat.le 1 0`; every closed `Rat` is normalized;
normalization calls `gcd`; `gcd`'s recursive step needs `mod_lt`, a theorem.

Two readings I ruled out rather than assumed:

- **not the sharing pass.** The error reports the type as a `let`-bound `_s7`,
  which invites a `zetaDelta` reading. Inlining every binding by hand (2,423-byte
  body) reproduces the identical refusal. (`set_option zetaDelta` is not an
  option name in 4.30.)
- **not a budget.** `maxRecDepth 1000000`, `maxHeartbeats 0` and
  `smartUnfolding false` each leave it exactly where it was, on the big file and
  on the two-line probe alike. `set_option diagnostics true` on the refused
  `gcd 1 1` shows the reducer unfolding `WellFounded.fix ↦ 2`, `Acc.rec ↦ 2`,
  `AxNat.gcd ↦ 2` and stopping: it gives up, it does not run out.

## 3. Fix or bound it — bounded, with the fix named and deferred

Nothing here is soundness-relevant, so the priority rule about a red `main` does
not fire. ADR-0517 records the decision: **the kernel is the checker we target**.

The fix is *known and measured*: emitting proofs as `def` makes the source route
carry the whole carrier in 27.9 s. It is **not taken here** for blast radius, not
doubt — it changes every artefact the repository ships (18 real-Lean suites read
the single-file front door), roughly doubles elaboration, and ADR-0458 has
modules declare whether they contain reasoning. `lean_pp.rs` had three lanes in
it today. The measurement is what the decision needs; the decision belongs to
the renderer's owner as its own ADR.

## 4. The coverage hole, closed

`real_lean_creal_carrier_kernel_replay` exports the **complete** checked
environment — no reachability filter — and replays it through Lean's kernel. Its
exit status depends on:

- Lean's reported final constant count **equalling** the count read out of our
  kernel (so "accepted" cannot mean "accepted a subset");
- the export still carrying `not_zero_one` and `not_le_one_zero` **by name**,
  asserted before any Lean runs;
- the tampered stream being rejected **naming `CReal.Equiv`**.

`real_lean_wellfounded_elaborator_divergence` pins the residue from the other
side, over the ℕ prelude alone, in four Lean invocations — including the
`theorem` → `def` rewrite of its own emitted module, which is what isolates the
mechanism to one token per line.

## Numbers in the handover that were wrong

| claim | measured |
| --- | --- |
| "465 declarations", "122 of 465" | the carrier is **470** on 2026-08-18 (`crates/axeyum-lean-kernel/src/creal/inverse.rs` had landed since); `examples/shared_prelude_module.rs`'s own doc comment says 445/280/165, a third figure. I did not re-measure the *reached* count, so 343/122 is repeated on the previous lane's authority |
| "Lean's kernel rejects them" | Lean's **elaborator** rejects them; Lean's kernel accepts all 470, in 1.4 s |
| "reproduces with sharing off, 7,187,035 B" | reproduces, yes — but with sharing ON the whole carrier is **2,541,928 B**, so the 7 MB figure is the sharing-off control and not the artefact |
| "`internal exception #3` is not a diagnosis" | correct, and it is not even a distinct failure |
| "`--include-constructed` is REQUIRED or those preludes are not built" | not exercised: nothing in this lane needed `nat_axiom_inventory` |

## Mutation checks

The two suites are separate integration-test binaries and each holds exactly
one `#[test]`, so a mutation confined to one file can only kill one test; what
is worth checking is that each mutation kills it *for the named reason* rather
than being absorbed. Both were also run against the *other* suite, which stayed
green, so neither death is a build-wide effect. Baseline before mutating:
`AXEYUM-CREAL-CARRIER declared=470 lean_kernel_constants=470`, `checked=2` and
`checked=4`, both suites `ok`.

**The first M1 attempt proved nothing and looked like it had.** The mutated code
used `str::Lines::rposition`, which does not compile (`Lines` is not
`ExactSizeIterator`), so `cargo test` emitted a compile error, the harness
printed no `test result:` line at all, and the grep that was watching for a
death found nothing to report — silence, in a slot where "the guard did not
fire" and "the mutation never ran" look identical. This is the repository's
signature defect one level down, in the mutation check itself: the re-run greps
`^error` as well, and the result below is from that re-run.

| mutation | tests that died |
| --- | --- |
| **M1** carrier replay: drop the LAST theorem record from the replayed stream. Lean still accepts it and `not_zero_one` is still present, so only the count moves. | **1**, at `real_lean_creal_carrier_kernel_replay.rs:235`: *"Lean's kernel ended with 469 constants where this kernel holds 470. A replay that admits a SUBSET is exactly the reachability hole this suite exists to close."* Lean still ACCEPTED the stream and the name-coverage precondition still passed, so the count-equality guard fired alone — it is what distinguishes "accepted" from "accepted a subset". The divergence suite stayed green (2.64 s). |
| **M2** divergence: make `theorems_as_defs` a no-op, so row 3 elaborates the unmodified module. | **1**, at `real_lean_wellfounded_elaborator_divergence.rs:331`: *"Lean's elaborator refused the module even with every proof spelled `def`, so the divergence is NOT the opacity of `theorem` and ADR-0517's account of it is wrong."* The carrier suite stayed green (115.00 s). |

## Left undone

- **The fix.** `theorem` → `def` in the renderer, measured to work on the whole
  carrier, deliberately left to the renderer's owner (ADR-0517).
- **A gate on the source-route residue itself.** The whole-carrier `.lean`
  elaboration takes 14 s and enumerates the four refusals in one pass; it is not
  wired into `check-lean-gate.sh`, because the kernel replay makes that number
  informational rather than load-bearing. If the `def` fix lands, this becomes
  the natural gate and the residue becomes zero.
- The structural-recursion `Nat.gcd`, per ADR-0517.
