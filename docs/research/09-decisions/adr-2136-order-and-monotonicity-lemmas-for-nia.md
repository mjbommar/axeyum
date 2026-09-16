# ADR-2136: order and monotonicity lemmas for QF_NIA — built, valid, and measured

Status: proposed
Index-summary: PLACEHOLDER — rewritten from the A/B before this ADR lands.
Index-status: proposed
Date: 2026-09-16

## Context

[ADR-2112] Part E inventoried our nonlinear-integer lemma portfolio against
z3's by the STEP each lemma takes rather than by its name, and found two
classes **absent** from `crates/axeyum-solver/src/nia_linearize.rs`:

- **order lemmas** — `nla_order_lemmas.cpp:286-310`, four sign-case
  implications coupling two monomials that share a factor;
- **monotonicity lemmas** — `nla_monotone_lemmas.cpp:61-90`, magnitude cuts
  taken at the current model assignment with no static bound.

Its Part D then measured, by **ablation on z3 itself**, that no single lemma
class is load-bearing for z3 on ≥ 15 of the 75 files z3 decides: the largest
is `nlsat` at 5, and the two classes above score 3 and — pooled with the rest —
no more. 66 of 75 files decide under every single-class removal. On that
evidence [ADR-2112]'s decision 4 says: do not build a single nonlinear lemma
class.

**That measurement is about z3's portfolio, not ours.** It says these classes
are redundant *for a solver that already has seven others*. Our portfolio has
four (sign, monomial bounds/McCormick, narrow-factor split, tangent), one of
which — the magnitude coupling — is conditioned on a static bound this
population does not have. So the open question [ADR-2112] did not answer is
what the two absent classes are worth **to us**, and answering it is a
measurement, not an argument.

Evidence, every script and per-row list:
[`bench-results/nia-order-lemmas-20260916/`](../../../bench-results/nia-order-lemmas-20260916/README.md).

## Part A — the sizing: is the step even available?

Before any code. `census_shared_factor.py` over all 116 undecided `QF_NIA` T1
rows (`bench-results/nia-trace-20260915/undecided-116.txt`), **116 files, 0
errored**, with applicability defined by the step each lemma takes:

| | files of 116 |
|---|---:|
| **order lemma applicable** (≥ 1 shared-factor product pair) | **111** |
| **monotonicity applicable** (≥ 1 product with an unbounded factor) | **115** |
| both | 111 |
| neither | 1 |

| per-file shape | min | median | p90 | max |
|---|---:|---:|---:|---:|
| nonlinear products | 0 | 242 | 1,911 | 38,472 |
| operands shared by ≥ 2 products | 0 | 53 | 239 | 2,924 |
| shared-factor product PAIRS | 0 | **2,249** | 44,415 | **9,407,886** |
| products with an unbounded factor | 0 | 242 | 1,911 | 38,472 |

Two numbers decided the design. Applicability is near-total, so neither class
is structurally inapplicable here — a live possibility, since 42 of these 116
never reach `cas-ideal-refuter` at all. And the candidate set is enormous, so a
static enumeration is out: emission has to be **model-driven and capped**,
which is also what z3 does.

The third number is the one that changed the plumbing: **`unbounded_products`
equals `products` at every quantile**. No product on this population has both
factors two-sidedly bounded, so `mccormick_lemmas` and `small_domain_lemmas`
produce nothing, and `RefinementSetup::refine` — which gates the whole
refinement loop on those having produced something — is false. Without a
change there, the loop runs ONE round on exactly the files this lane is aimed
at and the new pass is unreachable. See §C.

Controls: 8 fixtures, the census refuses to run if one fails, and an
independent check against the engine's own count — on the 89 rows carrying a
`nonlinear abstraction: N cross-products` detail (`nra.rs:567`, computed on the
normalized polynomial), both counts are nonzero on 89 of 89, 0 disagreements,
ratio median 1.00. The first join of those two files matched **0 rows** because
one path is corpus-relative and the other absolute; an empty overlap reads
exactly like total disagreement.

## Part B — the design claims, at `file:line` on all three sides

| step | z3 | cvc5 | ours (after this ADR) |
|---|---|---|---|
| order: couple two products sharing a factor | `nla_order_lemmas.cpp::generate_ol` `:286-310`, selected at the model by `order_lemma_on_ac_and_bc_and_factors` `:322-341`; the equality case `generate_ol_eq` `:265-284` | `monomial_bounds_check.cpp:308-325` — multiply an asserted inequality through by a term of known model sign, REVERSING the relation when that sign is negative (`infer_type`, `:308`); gated on the inferred fact being false at the current abstract model (`:317`) | `order_lemma_at_model`, `order_eq_lemma_at_model` |
| monotonicity: magnitude cuts at the assignment | `nla_monotone_lemmas.cpp::monotonicity_lemma_lt` `:80-90`, `::monotonicity_lemma_gt` `:61-72`, dispatched by `::monotonicity_lemma(monic const&)` `:23-39` | `monomial_check.cpp::checkMagnitude` `:193`, ordering monomials by the ABSOLUTE value of their abstract model values (`assignOrderIds(..., isAbsolute=true)`, `:202`) and emitting through `compareMonomial` `:517` | `monotone_lemmas_at_model` |
| magnitude atom without an `abs` term | `nla_basics_lemmas.cpp::negate_strict_sign` `:202-216` — replace the magnitude atom by a STRICT SIGN literal keyed off the current value's sign | — | the same: plain linear atoms against integer constants read from the model |
| tangent planes (already present) | `nla_tangent_lemmas.cpp` | `tangent_plane_check.cpp:37` | `tangent_lemmas` (`nia_linearize.rs:1732`) |

### B1 — why no `abs` term is needed, stated as the soundness argument

[ADR-2112] E1 noted that `nia_linearize.rs` contains **no IR magnitude term at
all**, and that both absent classes are stated on `|·|`. z3 does not build one
either, and the reason is not an encoding trick: the hypothesis literals it
emits pin the SIGN as well as the magnitude, so the product's sign is
determined and the two-sided `|m| ≥ |p|` collapses to a one-sided linear
comparison. Concretely, for `r ≈ a·b` at model values `(a_val, b_val)` with
`p = a_val·b_val` and neither factor zero:

```text
|r| too SMALL:  (a_val<0 ? a ≤ a_val : a ≥ a_val)
              ∧ (b_val<0 ? b ≤ b_val : b ≥ b_val)   →  (p<0 ? r ≤ p : r ≥ p)

|r| too LARGE:  (a_val<0 ? a_val ≤ a ≤ 0 : 0 ≤ a ≤ a_val)
              ∧ (b_val<0 ? b_val ≤ b ≤ 0 : 0 ≤ b ≤ b_val)
                                                     →  (p>0 ? r ≤ p : r ≥ p)
```

The second half of each `gt` hypothesis — the `a ≤ 0` / `0 ≤ a` — is the sign
pin, and it is not decoration. `monotone_gt_without_the_sign_pin_is_refutable`
constructs the weakened lemma by hand and shows the validity checker refutes
it: without the pin the hypothesis admits a factor of the opposite sign and
unbounded magnitude, and the conclusion is false there.

The order lemma's four cases collapse the same way. With `rac` and `rbc` the
abstraction variables for `a·c` and `b·c`:

```text
c > 0 ∧ ac ≥ bc → a ≥ b        c < 0 ∧ ac ≥ bc → a ≤ b
c > 0 ∧ ac ≤ bc → a ≤ b        c < 0 ∧ ac ≤ bc → a ≥ b
```

— the sign of `c`'s model value picks the first hypothesis, the relation the
model exhibits between the two ABSTRACTION values picks the second (not between
the products: the whole point is that the relaxation's `r` need not equal
`a·c`), and the lemma is emitted only when the model violates the conclusion.
`c = 0` emits nothing; `rac = rbc` is the equality case `c ≠ 0 ∧ ac = bc → a = b`,
which the four ordered implications structurally cannot reach.

**Every lemma is a consequence of `r = a·b` alone.** It is therefore true in
every integer model of the ORIGINAL query, exactly like the sign and tangent
lemmas: adding it can only shrink the relaxation's model space, an `unsat`
still transfers, and a `sat` is still accepted only after `replay_sat` against
the original assertions.

## Part C — what arming changes beyond the lemmas

`RefinementSetup::refine` gates the refinement loop on `mccormick + splits > 0`,
and §A measured that this population produces neither. Arming therefore also
widens that predicate:

```rust
refine: mccormick + splits > 0 || (order_lemmas && !rewritten_triples.is_empty()),
```

This is a real behavioural change and it is named here rather than buried: the
order and monotonicity lemmas need no static bound at all — that is
[ADR-2112] E1's second design claim — so on an armed run a product is itself
structure for a lemma to bite on. It also grants the loop the larger budget
slice `refine` selects. Both are behind the lever.

## Part D — the A/B

PLACEHOLDER — filled from `bench-results/nia-order-lemmas-20260916/` before
this ADR lands.

## Decision

PLACEHOLDER — filled from Part D.

## Gates, with counts

PLACEHOLDER.

## Consequences

PLACEHOLDER.

[ADR-2112]: adr-2112-qf-nia-what-the-clause-estimate-counts.md
[ADR-2106]: adr-2106-derived-ladder-order.md
