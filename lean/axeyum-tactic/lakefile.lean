import Lake
open Lake DSL

/-!
`by axeyum` — a Lean tactic that asks Axeyum for a proof term and hands the
term to Lean's own elaborator and kernel.

No Mathlib dependency in v1, deliberately: the whole point is that the terms
Axeyum emits are checkable against Lean *core*, and a Mathlib dependency would
make it impossible to tell whether a goal closed because core admitted the term
or because Mathlib's simp set did the work. See ADR-1666.

`Tests` is a separate library rather than a `lean_exe` or a script because the
tests ARE the acceptance gate: every one is a goal Lean either elaborates or
does not, and `lake build Tests` failing is the gate failing. It needs
`AXEYUM_SIDECAR` in the environment; `scripts/check-lean-tactic.sh` sets it,
counts what the build printed, and enforces the floors.
-/

package «axeyum-tactic» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Axeyum where
  roots := #[`Axeyum.Shim, `Axeyum.Protocol, `Axeyum.Tactic]

@[default_target]
lean_lib Tests where
  roots := #[`Tests.NatLinear, `Tests.Mutations, `Tests.ShimCorrespondence]
