# What capability comes after equality: the 15 producer-decline goals, by shape

Date: 2026-08-22

Source: the frozen 2026-08-19 reflexivity census
([`22-mathlib-reflexivity-coverage.md`](22-mathlib-reflexivity-coverage.md)),
re-read from `observation.json` under the hash-pinned external root.
Plan: [`226`](226-production-measurement-and-general-producer-plan.md) P4.

## Why this exists

The census recorded four outcomes over 138 frozen statements and nobody had
looked at what the middle bucket actually contains:

```text
adapter-rejection:trusted-declaration          114
producer-decline:terminal-not-exact-equality    15
kernel-rejection:candidate-typecheck-failed      7
admissible-proof                                 2
```

`producer-decline` means the statement adapter succeeded and the producer then
refused, because it only knows how to propose `Eq.refl` and the goal's terminal
relation is not an equality. **Which relation it is instead determines what
capability the project should build after equality**, and that was unrecorded.

## The shapes

| Shape | Count |
|---|---:|
| inequality (`<`, `≤`, `>`, `≥`) | **8** |
| biconditional (`↔`) | **4** |
| divisibility (`∣`) | **2** |
| negation (`≠`) | **1** |
| implication · conjunction · disjunction · existential | 0 |

All 15 are `train` partition; **none is held-out**. Families are
`natural-factorial` (7) and `natural-fibonacci` (8).

| Shape | Fact | Family | Statement |
|---|---|---|---|
| `biconditional` | `F:ml430-mutation-1432b2277cf2cc26c1d11cd6` | natural-fibonacci | `∀ {n : ℕ}, Nat.fib n = 0 ↔ n = 0 ∨ n = 1` |
| `biconditional` | `F:ml430-nat-fib-eq-zero-61879073` | natural-fibonacci | `∀ {n : ℕ}, Nat.fib n = 0 ↔ n = 0` |
| `biconditional` | `F:ml430-nat-fib-lt-fib-3582b881` | natural-fibonacci | `∀ {m : ℕ}, 2 ≤ m → ∀ {n : ℕ}, Nat.fib m < Nat.fib n ↔ m < n` |
| `biconditional` | `F:ml430-nat-fib-pos-9e67bd8e` | natural-fibonacci | `∀ {n : ℕ}, 0 < Nat.fib n ↔ 0 < n` |
| `divisibility` | `F:ml430-nat-factorial-dvd-factorial-e9d14845` | natural-factorial | `∀ {m n : ℕ}, m ≤ n → m.factorial ∣ n.factorial` |
| `divisibility` | `F:ml430-nat-fib-dvd-f80f3de1` | natural-fibonacci | `∀ (m n : ℕ), m ∣ n → Nat.fib m ∣ Nat.fib n` |
| `inequality` | `F:ml430-nat-descfactorial-le-2b8cc09a` | natural-factorial | `∀ (n : ℕ) {k m : ℕ}, k ≤ m → k.descFactorial n ≤ m.descFactorial n` |
| `inequality` | `F:ml430-nat-factorial-le-d0f4a912` | natural-factorial | `∀ {m n : ℕ}, m ≤ n → m.factorial ≤ n.factorial` |
| `inequality` | `F:ml430-nat-factorial-lt-of-lt-d6c2125d` | natural-factorial | `∀ {m n : ℕ}, 0 < n → n < m → n.factorial < m.factorial` |
| `inequality` | `F:ml430-nat-factorial-pos-f1dd2405` | natural-factorial | `∀ (n : ℕ), 0 < n.factorial` |
| `inequality` | `F:ml430-nat-fib-le-fib-succ-d1ef4a3d` | natural-fibonacci | `∀ {n : ℕ}, Nat.fib n ≤ Nat.fib (n + 1)` |
| `inequality` | `F:ml430-nat-le-fib-add-one-5284f0bf` | natural-fibonacci | `∀ (n : ℕ), n ≤ Nat.fib n + 1` |
| `inequality` | `F:ml430-nat-le-fib-self-0cbccb4d` | natural-fibonacci | `∀ {n : ℕ}, 5 ≤ n → n ≤ Nat.fib n` |
| `inequality` | `F:ml430-nat-self-le-factorial-cfdffc69` | natural-factorial | `∀ (n : ℕ), n ≤ n.factorial` |
| `negation` | `F:ml430-nat-factorial-ne-zero-5fc0b0a1` | natural-factorial | `∀ (n : ℕ), n.factorial ≠ 0` |

## What it says about sequencing

Taken with the 7 `kernel-rejection` rows — goals that *are* equalities but not
*definitional* ones — the queue past bare reflexivity is stratified, and the
strata are unequal:

| Capability | Unlocks | Notes |
|---|---:|---|
| equality by bounded rewriting with existing lemmas | up to 5 | the `kernel-rejection` cluster, minus one false mutation and one already proved |
| inequality reasoning over `Nat` | 8 | the largest single stratum here |
| biconditional splitting (`↔` → two implications) | 4 | reduces to the strata above |
| divisibility | 2 | `factorial ∣ factorial`, `fib ∣ fib` |
| `≠` via `0 <` | 1 | collapses into inequality |

Inequality is the biggest lever *in this bucket*. It is **not** the biggest lever
overall, and the census says so plainly: `adapter-rejection` is **114 of 138**,
so 83% of the population never reaches a producer at all. Building inequality
reasoning would address 8 rows; unblocking the adapter addresses 114. This table
sequences the work that becomes reachable *after* that, and should not be read as
the top priority.

## Limits

The shape label is assigned by reading the terminal relation of
`formal.statement` after stripping binders and hypotheses. It is a syntactic
classification of the *statement*, not of the proof each would need — `≠` is
listed separately from inequality even though `n! ≠ 0` and `0 < n!` are the same
obligation in practice.

## Provenance

Produced by a Haiku subagent under a mechanical brief that required a positive
control (the 138-row outcome counts had to reproduce 114/15/7/2 before any table
could be reported), then independently recounted here before landing: shape
totals and the zero held-out count both reproduce exactly.

That pairing is the point. The same model, on a task that required judging
whether a tool had measured what it claimed, produced a confident false finding
the day before ([`231`](231-weak-model-flywheel-experiment.md)). Mechanical
extraction with a mandatory positive control is where it is reliable.
