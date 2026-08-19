# 03 — Values versus theorems

**The campaign's own verdict on itself.** Twelve hours, seven agents, the whole
stack pointed at open mathematics. Output: **18 new off-diagonal Schur numbers,
2 new Rado numbers, and zero theorems.**

Asked whether that was real mathematics, the honest answer was no — the values
were *predicted in advance by a published conjecture and confirmed*. `S(3;4,4,u)`
is exactly `11u − 1` for `u = 4..13`; six of the eighteen sit on that straight
line. Every one was a data point the formula already specified.

This document is about why that happened and what changes it.

## The one thing that was not a value

The `∀`-route proved the `k=2` Rado case **for symbolic `a` and `b`** over
unbounded ℤ, without assuming `b < a`. That is a statement about an **infinite
family** — a theorem, not a table entry — and it is the only such result the
project has.

`k=3` is **1 of 3 cases**. That is the frontier of rung 4.

## What was actually blocking k=3, measured

The register recorded the obstacle as *"degree-3/4 inequalities in three
variables"* — i.e. a missing nonlinear engine. Measured on 2026-08-14, that is
**false**: those inequalities prove in **2 ms** with a firing control.

Three findings replaced it, all measured:

**1. The blocker is integer rounding of a nonlinear bound.**

```
P ≥ 1, P·s ≥ P+1  ⊢  s ≥ 2      unknown
                  ⊢  s > 1       0 ms
       s > 1      ⊢  s ≥ 2       0 ms
```

Each half is instant; the composition is not. The fix is a normalisation —
`x ≥ k ↔ x > k−1` over `Sort::Int`, retried on `unknown` — plus a
product-abstraction weakening pass, both measured as `unknown`-at-20s → **0 ms**.

**2. The case analysis is far smaller than recorded.** An independent
enumeration found **one** leaf where `b < a` can matter, not ten. The critical
leaf's arithmetic core discharges step by step: 7 lemmas, ≤ 2 ms each, controls
firing, once `a·b` is abstracted.

**3. The failure is not a budget.** `MAX_CROSS_PRODUCTS = 2` at `nra.rs:107` is
a deterministic admission cap: the query declines in **40 ms at 1 s, 10 s, 60 s
and 300 s alike**, and stays `unknown` through the 1800 s rung. Budget is
irrelevant *by construction* — which is a stronger and more actionable statement
than "it times out".

**k=3 is not proved.** The composition and twelve leaves are unencoded. But the
remaining work changed shape: from *"we need a better nonlinear engine"* to two
named passes and an encoding effort.

## Why the stack produces values and not theorems

Three structural reasons, in order of how much they bind:

**A finite problem is a formula; an infinite family is a statement.** A Rado
number at `n = 741` is 2,964 Boolean variables and a DRAT certificate. `R_k(a) =
a^k for all k` has no CNF. Rung 4 needs quantified reasoning over symbolic
parameters, and that route exists but is narrow.

**Hypothesis sets defeat it, and that was misdiagnosed as difficulty.** Every
monolithic query carrying a full hypothesis set returned `unknown` — 8 of 8 —
while the same content split into 3–4-hypothesis lemmas closed in **0.00 s**.
Automatic hypothesis minimisation now finds those subsets in ~2 s, and finds
**exactly the ones a human found after four attempts and 32 minutes**. But the
whole colour-1 case still fails: it needs a **chain of lemmas, not a subset**.
That is the next real capability — composition of proof steps, not selection
among hypotheses.

**There is nothing to state a theorem *in*.** See
[`02`](02-the-library.md). ℤ is axiomatized. A theorem about integers, in a
kernel where ℤ is three assumptions, inherits them.

> **Overtaken 2026-08-16/19.** That was the binding reason at the time and it no
> longer holds: `integer` is **0 trusted declarations, 57 derived**
> (`--example int_theorem_inventory`), and the ladder now runs ℕ → ℤ → ℚ → ℝ → ℂ
> with every one of those preludes at trusted surface 0. So a symbolic-integer
> theorem no longer inherits postulates. The *other* two reasons in this section
> — a finite problem is a formula, and hypothesis chains rather than hypothesis
> subsets — were not about the library and are untouched by it. They are now the
> whole of the answer, which makes this section's diagnosis sharper than when it
> was written, not weaker.

## What would change it

1. **The two named passes** (integer bound strictness, product abstraction).
   Small, measured, and they close the critical leaf.
2. **Lemma chaining, not just lemma selection.** Minimisation finds a sufficient
   subset; it cannot build a derivation. The colour-1 case is the concrete
   target and it is a genuinely new capability.
3. ~~**ℤ constructed rather than assumed**~~ — **done 2026-08-16** (0 axioms),
   and the constructed ladder now reaches ℂ. A symbolic-integer theorem no longer
   rests on postulates; what it still lacks is the chaining in item 2.
4. **A certificate for the result.** A symbolic theorem discharged with a
   re-checkable artifact is rung 3 and rung 4 at once — and nobody has
   demonstrated that in this problem space.

## The test

**One statement with symbolic integer parameters, proved, with a certificate an
independent kernel accepts.**

Not eighteen more values. The values were worth having — 30 independent
reproductions of published numbers with zero disagreements is a real statement
about the encoder, the solver and the checker — but they are the *floor* of what
this architecture is for, and the campaign showed the floor is solid.

The ceiling is a theorem, and it is one library and two rewrite passes away
rather than an engine away. **The library arrived** (2026-08-16/19, ℕ → ℤ → ℚ →
ℝ → ℂ, every prelude at trusted surface 0); the two rewrite passes are still the
outstanding half. That is a much better position than the register
described, and it was only discoverable by measuring the thing everyone assumed.
