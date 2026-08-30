# ADR-0825: For a decidable subject, row 1 and row 3 can be the same kernel statement, executed twice

Status: accepted
Date: 2026-08-30
Index-summary: A graded statement family over a decidable carrier (ADR-0716) does not need a separate row-3 producer/verifier pair when the row-1 theorem itself is executable at any concrete instance — instantiating the same declaration at discriminating numerals, with a genuine kernel rejection at a non-instance, is row 3, landed as `Nat.not_prime_of_pow_mod_ne`.
Index-status: accepted

## Context

[ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
splits a classical theorem into up to four rows. [ADR-0716](adr-0716-row-two-of-a-decidable-subject.md)
established that for ℕ/ℤ/ℚ the analysis-style row 2 is provably empty (the
decision principle every such row extracts — order totality — is already a
proved, axiom-free theorem here), and that row 3 for number theory is the
axis the dominance argument has to move onto — and named it as "mostly
unbuilt": `axeyum-cas`'s `is_prime`, `factorize`, `mod_inverse`, `crt`,
`legendre_symbol` are bare computation with no witness type and no verifier.

ADR-0716 also named a specific target as "one theorem away":
`a^phi(n) = 1 (mod n)` (Euler's theorem), citing two already-landed
ingredients (`Int.euler_unit_coprime`, `Int.euler_unit_injective`). This
lane verified that claim in-tree before starting (per the standing
"a handoff's blocked-on-X is a claim about one route" rule) and found it
false: `int_prelude/euler_totient.rs`'s own module doc records, in detail,
that the theorem does NOT land there — a subset-restricted product and its
permutation-invariance lemma were both missing at the time it was written —
and a sibling lane's handoff (`docs/plan/status/374-euler-theorem.md`,
`int_prelude/euler_theorem.rs`) had already built the cheap half of the fix
(`Int.prodRangeIf`/`Int.prodRangeIf_permute`, routing around the missing
`Nat.prodRange` swap induction by working over `Int.prodRange_permute`
instead) and left three genuinely hard pieces open: an `Int`/`Nat` index
bridge, the unproved converse of `Int.euler_unit_coprime`, and the final
assembly (a new induction, pointwise factoring, `ModEq` transport, and a
cancellation argument). Separately, `nat_prelude/perfect.rs` (3,702 lines)
is under active multi-lane construction toward the Euclid–Euler even-perfect-
number theorem (Euclid IX.36), with `Nat.sumDivisors_two_pow` and
`Nat.dvd_two_pow_mul_classify` landed and the final assembly not yet wired
into `declare_perfect_all`.

Both are real, valuable targets. Neither is a one-session task, and both
have active or recent lane investment this session should not duplicate or
collide with (CLAUDE.md's multi-agent hygiene section: touching a large,
actively-developed file with unfamiliar internal architecture is a genuine
collision risk, not merely a duplication-of-effort risk).

## Decision

Land a smaller, self-contained family instead, chosen specifically because
it demonstrates a shape ADR-0716 did not name: **for a decidable subject,
row 1 and row 3 do not have to be two different artifacts.** They can be
literally the same kernel declaration — one used symbolically (row 1), one
instantiated at concrete numerals and kernel-checked, including a genuine
rejection at a non-instance (row 3) — with no separate `axeyum-cas`
producer/verifier pair required.

`Nat.not_prime_of_pow_mod_ne : ∀ p a, Not (Eq (modulo (pow a p) p)
(modulo a p)) → Not (Prime p)` is Fermat's little theorem
(`Nat.pow_prime_modeq_self`, already landed, 0 axioms) run backwards: the
Fermat compositeness test's whole engine, a plain modus-tollens step.
Building it needed one new piece of infrastructure,
`Nat.mod_eq_iff_mod_eq : ∀ d a b, 0 < d → Iff (ModEq d a b) (Eq (modulo a
d) (modulo b d))`, which bridges `Nat.ModEq`'s existential balanced-witness
definition (not itself refutable by kernel reduction — its negation
quantifies over every witness pair) to the executable `Nat.mod` comparison,
by composing two already-landed theorems
(`Nat.mod_eq_iff_div_mod_remainder_eq`, `Nat.div_mod_exec`) with no new
induction.

**Row 2 does not apply**, for the ADR-0716 reason: the statement is a
single logical step on an unconditional theorem, with no comparison and no
unbounded search to reduce to a boundary. This is argued from the shape of
the proof, not asserted.

**Row 3 is the row-1 declaration itself, instantiated twice and kernel-
checked both ways**: at the composite witness `p := 4, a := 3`
(`3^4 mod 4 = 1 ≠ 3 mod 4 = 3`), the resulting `Not (Prime 4)` is admitted
as a throwaway theorem — a genuine, executable compositeness certificate.
At the real prime `p := 5, a := 3` (`3^5 mod 5 = 3 = 3 mod 5`), the
identical construction is attempted and the trusted kernel gate REFUSES
it, because `Eq.refl` cannot certify a `Bool` computation that reduces to
`true` as `false`. This is the non-vacuity control ADR-0603's row-3
discipline (and this repository's "a checker that cannot fail is worse
than no checker" standing rule) requires: the check genuinely depends on
the arithmetic outcome.

Both declarations are axiom-free, measured from the kernel
(`theorem_axiom_footprint`, footprint `[]` for each, against the whole Nat
prelude's 727 theorems all axiom-free).

## Consequences

- **A decidable-subject family does not automatically need
  `axeyum-cas` involvement to have a real row 3.** ADR-0716 §4's list of
  what number theory's row 3 needs (a witness type and a verifier sharing
  no code with the producer, for primality/factorization/CRT/Legendre)
  still stands for those specific targets, whose row-1 statements are not
  themselves directly executable at scale the way a single modus-tollens
  step is. This ADR narrows the claim to: **check whether the row-1
  declaration is directly executable before reaching for a separate
  producer/verifier pair** — it sometimes is, and when it is, that is the
  cheaper and equally honest row 3.
- **Verifying a handoff's "blocked on X" cost this lane nothing it would not
  have spent anyway**, and it prevented dispatching effort at a target two
  other lanes had already measured as harder than advertised, or duplicating
  work inside a file three other commits were actively extending the same
  session. Recorded in
  [`docs/plan/status/graded-families-number-theory.md`](../../plan/status/graded-families-number-theory.md).
- Facts: `F:nat-mod-eq-iff-mod-eq`, `F:nat-not-prime-of-pow-mod-ne`.
