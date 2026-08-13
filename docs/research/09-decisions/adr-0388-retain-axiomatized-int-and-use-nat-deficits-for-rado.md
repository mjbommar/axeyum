# ADR-0388: Retain the axiomatized Int profile and use Nat deficits for Rado rigidity

Status: accepted

Date: 2026-08-13

Requirements:
[`lean-kernel-requirements-2026-08-13.md`](../../plan/lean-kernel-requirements-2026-08-13.md),
R2 / R7.2.

Closes: Q3 and the integer-foundation part of Q5 in
[`research-questions.md`](../08-planning/research-questions.md).

## Context

Axeyum has two distinct integer needs which must not share an implicit trust
claim. Solver reconstruction already uses the ADR-0042 `Int` profile: 34
kernel axioms comprising a carrier and operations, standard ordered-ring and
discreteness assumptions, and four declarations classified for later
discharge. That profile has proved useful for checking integer-infeasibility
certificates, but it is not a construction of the integers.

The Rado/Ramsey paper has a different requirement. Its current 14-theorem
Lean-syntax export is entirely over the zero-axiom Nat development. The novel
`M = N+1` half of `thm:rigid` is not yet formalized. The hand proof writes
signed block defects `e_c = w_c - L_c` and partial sums `E_j`, so a direct
translation could use the 34-assumption Int profile. Doing so would make the
paper's existing "no axiom" description false for the new theorem.

Constructing `Int` as a quotient is not a zero-axiom escape. Lean 4.30's
privileged quotient package has exactly four declarations: `Quot`, `Quot.mk`,
`Quot.lift`, and `Quot.ind`. `Quot.sound` is a separate ordinary axiom in an
exported environment. Axeyum implements and tests the four-member package, but
ADR-0365 correctly remains proposed because its pinned-Lean M4 differential is
open. Adding `Quot.sound` and then building the integer library would replace
34 Int-profile assumptions with a much larger construction while still
retaining one framework axiom. It is not justified by the Rado proof.

## Decision

**Retain `build_int_prelude` as an explicitly axiomatized, reconstruction-only
profile; do not construct a second native integer library now; and formalize
the Rado `M = N+1` rigidity argument first with a Nat-valued prefix-deficit
invariant.**

The following boundaries are mandatory:

1. Every result whose checked dependency closure touches `build_int_prelude`
   states that it relies on 34 assumptions. "No axiom" and "zero axiom" are
   prohibited for that closure even if all theorem-specific hypotheses and
   proof terms are explicit.
2. The 34-row integer population remains in the generated axiom ledger and is
   linked to this decision. R2 does not discharge or reclassify a row.
3. The Rado publication lane does not use `build_int_prelude`. Its first
   `thm:rigid` target is the separable `M = N+1` half, expressed with prefix
   widths rather than signed subtraction.
4. Let `A_j = sum_{c=2..j} w_c` and
   `C_j = sum_{c=2..j} L_c`. The induction invariant is `A_j <= C_j`. If
   `w_j <= L_j`, monotonicity advances it. In the only remaining width case,
   `w_j = L_j + 1`, the obstruction trigger gives `a | A_{j-1} + 1`, while
   the canonical closed form gives `a | C_{j-1}`. Equality of the prefixes
   would imply `a | 1`, contradicting `a >= 2`; hence the previous prefix has
   the one unit of slack needed to advance the invariant.
5. At the core, `W <= L_k` contradicts the `N+1` budget using
   `A_{k-1} <= C_{k-1}`. If `W = L_k + 1`, the budget forces prefix equality,
   while the core trigger again implies `a | 1`. This is the signed proof's
   exact contradiction without `Int`, negative values, or truncated
   subtraction in the theorem statement.
6. ADR-0365 remains a Lean-conformance decision. It may be accepted only after
   its own M4 evidence, not as a shortcut for this theorem. A future
   quotient-constructed integer library requires a new ADR, an explicitly
   ledgered `Quot.sound`, and a measured consumer that repays the library cost.
7. Importing Mathlib integers remains governed by R5 and requires its separate
   trust decision for `propext`, `Quot.sound`, and `Classical.choice`.

## Evidence

- The runtime-derived ledger contains exactly 34 `integer` rows: 8 primitive
  interfaces, 22 retained external assumptions, and 4 planned derivable
  theorems.
- ADR-0042 and the current reconstruction routes already depend on that
  profile, so removing it would regress an established checker surface without
  helping the Rado theorem.
- ADR-0365 and its M1--M3 result identify the official quotient package as four
  members and explicitly classify a later `Quot.sound` as an ordinary ledgered
  axiom.
- The paper's Appendix B proof uses signed defects only to maintain the prefix
  nonpositivity invariant `E_j <= 0`. The equivalent `A_j <= C_j` invariant
  above uses the same width bound, divisibility trigger, canonical congruence,
  and final budget contradiction, but stays in Nat.
- The current paper says its existing export has no axiom and has not been
  checked by real Lean. It does not claim that `thm:rigid` is among those
  exported theorems, so retaining the Nat-only boundary requires no paper-text
  change at this decision point.

## Alternatives

### Use the existing axiomatized Int profile for `thm:rigid`

Rejected for the credited Rado lane. It is the shortest encoding, but it turns
one of the paper's distinguishing assurance claims into a 34-assumption result
when a direct Nat invariant expresses the same proof.

### Add `Quot.sound` and construct Int now

Rejected. This does not yield an absolutely axiom-free development, does not
close ADR-0365's official differential, and commits to a large integer library
before the selected theorem needs one.

### Maintain both Rado encodings before choosing

Rejected as a gate. A second 34-assumption formalization would measure proof
engineering cost but would not strengthen the zero-axiom result. It may be run
later as a non-crediting comparison after the Nat theorem exists.

### Avoid deciding and let each caller choose a prelude

Rejected by R2. The resulting trust claim would depend on construction order
and call-site convention rather than a reviewable publication boundary.

## Consequences

The existing solver reconstruction surface and its 34 assumptions remain
unchanged. The Rado lane receives a precise, zero-axiom-compatible encoding and
can proceed to the missing Nat order, divisibility, congruence, finite-sum, and
interval library without building integers first. The quotient conformance
work remains valuable but no longer blocks the Rado theorem.

This closes the R2 foundation choice and R7.2 encoding choice; it does not
prove the width lemma, the prefix invariant, or either half of `thm:rigid`.
Those remain R4/R7 implementation work and must retain the paper's current
official-Lean disclosure until R0.2 is independently closed.
