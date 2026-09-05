import Lean
import Axeyum.Tactic
/-!
# Fragment 2 — the mutation battery

Same eight categories as C3's goal pack
(`artifacts/lean-adapter/goal-pack/thin-adapter-v1.json`, ADR-0935), asked of
the Lean side instead of the Rust side. Each one points `by axeyum` at a stub
sidecar that misbehaves in exactly one way, and each one must FAIL.

The distinction the battery exists to draw, and the reason it is worth running
at all: **which side rejected.**

| category | rejected by | why that is the interesting answer |
|---|---|---|
| `unknown` / `timeout` / `unsupported` | the protocol check | a typed decline, reported as such, never a `sorry` |
| `malformed_response` | the protocol check | an unrecognized envelope must not read as a decision |
| `wrong_environment` | the protocol check | a stale or substituted identity |
| `wrong_goal` | **Lean** | the sidecar returns a term that is a perfectly good proof — *of something else*. The envelope is flawless. Only elaborating at the goal's own type catches it. |
| `mutated_proof` | **Lean** | a term that is not a proof of anything. The envelope is flawless. |
| `not_a_term` | **Lean** | text that is not a term at all |
| `sorry_term` | **Lean** | the one thing a dishonest sidecar would most like to send |

The last three are the point of the whole design. `wrong_goal`,
`mutated_proof`, `not_a_term` and `sorry_term` all arrive with a well-formed
`accepted` envelope carrying the correct environment identity — every
Rust-side and protocol-side check *passes* — and the goal still does not
close, because the only thing that closes a goal here is a term Lean's own
elaborator and kernel accepted.

`#guard_msgs` pins each failure's message, so a mutation that started being
accepted, or that started failing for a *different* reason, fails this file.

The stubs are in `Tests/stubs/`; each is a two-line shell script that ignores
its input and prints one fixed response.
-/

set_option linter.unusedVariables false

namespace Tests.Mutations

/-! ## Rejected by the protocol check -/

/-- error: axeyum: declined: unknown -/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/declined-unknown.sh"

/-- error: axeyum: declined: timeout -/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/declined-timeout.sh"

/-- error: axeyum: declined: unsupported -/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/declined-unsupported.sh"

/-- error: axeyum: malformed-response: not JSON: offset 0: expected: null -/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/malformed-not-json.sh"

/--
error: axeyum: malformed-response: unrecognized decline reason because-i-said-so
-/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/malformed-bad-reason.sh"

/-- error: axeyum: malformed-response: unrecognized status maybe -/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/malformed-bad-status.sh"

/-! ## Rejected by Lean, with a flawless envelope

Each stub below sends `status: accepted` with the environment identity the
request carried. Nothing on the protocol side has anything to object to. -/

/-! The environment-identity check catches a *stale* or substituted identity.
It is not a soundness mechanism: an honest sidecar simply echoes the identity
the request carried, so this check can only fire on a response that did not.
That limit is ADR-0935's, restated for the tactic in ADR-1666. -/

/--
error: axeyum: wrong-environment: response claims lean-4.9.0:axeyum-tactic-v1, request carried lean-4.34.0-rc1:axeyum-tactic-v1
-/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/wrong-environment.sh"

/-! `wrong_goal`: the term is a **true theorem** Lean is perfectly happy with —
it is just not this goal. The envelope is flawless. Nothing short of
elaborating at the goal's own type distinguishes it. -/

/--
error: axeyum: term-rejected-by-lean: Type mismatch
  Axeyum.Shim.natAddComm a b
has type
  a.add b = b.add a
but is expected to have type
  a ≤ a + b
-/
#guard_msgs in
example (a b : Nat) : a ≤ a + b := by axeyum "Tests/stubs/wrong-goal.sh"

/-! `mutated_proof`: a REAL emitted term with one argument changed, so it is a
proof of nothing. The envelope is flawless. -/

/--
error: axeyum: term-rejected-by-lean: Type mismatch
  fun axb1 => a.add b = axb0
has type
  a.add b = axb0 → Prop
but is expected to have type
  a.mul b = axb0 → Prop
-/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/mutated-proof.sh"

/-! `not_a_term`: the response's `term` is text that does not parse. -/

/--
error: axeyum: term-did-not-parse: <axeyum-sidecar-response>:1:12: expected end of input
-/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/not-a-term.sh"

/-! `sorry_term`: the response's `term` is `sorry`. This is the mutation a
dishonest sidecar most wants to get away with, and it is refused explicitly
rather than incidentally — `Axeyum.assignTerm` checks `hasSorry` first. -/

/-- error: axeyum: term-rejected-by-lean: the term mentions sorryAx -/
#guard_msgs in
example (a b : Nat) : a + b = b + a := by axeyum "Tests/stubs/sorry-term.sh"

/-! ## The positive control

Without this, every test above would still pass with a tactic that always
fails. This is the same goal, through the real sidecar, and it must CLOSE. -/

theorem control_the_real_sidecar_still_closes_the_goal (a b : Nat) :
    a + b = b + a := by axeyum

#print axioms control_the_real_sidecar_still_closes_the_goal

/-! ## The counts

The number of *rejections* is NOT printed from here: a literal in this block
would measure the author's memory, and Lean cannot count its own
`#guard_msgs` blocks. `scripts/check-lean-tactic.sh` counts them by reading
this file — the authority — and enforces a floor, while this file elaborating
at all is what says every one of them matched. The control count is read from
the environment, because Lean can see that. -/

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut controls := 0
  for (name, info) in env.constants.toList do
    if name.getPrefix == `Tests.Mutations && !name.isInternal then
      match info with
      | .thmInfo _ => controls := controls + 1
      | _ => pure ()
  Lean.logInfo s!"AXEYUM-TACTIC-MUTATIONS controls={controls}"

end Tests.Mutations
