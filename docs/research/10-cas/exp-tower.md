# Design note: the exponential-tower substrate (`eᴬ·eᴮ = eᴬ⁺ᴮ` in the zero-test)

Status: design (2026-07-21)

## The problem

The zero-test ([`equal`](../../../crates/axeyum-cas/src/lib.rs)) normalizes an
expression to a `MultiPoly` over **opaque transcendental atoms**: a head `f(arg)`
becomes a fresh variable keyed `\0f:<render(arg)>` (see `atom_name`). This is sound
and lets differentiation/integration/summation of transcendental-bearing results
certify — *as long as* each atom appears independently.

It breaks for the **exponent law**. `exp(A)` and `exp(B)` are independent atoms
(distinct keys), so their product `exp(A)·exp(B)` is a two-variable monomial that
the zero-test never reduces to `exp(A+B)`. Consequences, all confirmed by
measurement:

- **First-order linear ODEs** (integrating factor): the certificate needs
  `e^{−P}·e^{P} = 1`. Declines.
- **Linear recurrence closed forms**: `rⁿ = e^{n ln r}`, and the recurrence check
  needs `e^{n ln r}·e^{−ln r} = e^{(n−1)ln r}`. Not representable/decidable.
- **Gosper geometric fragment**: `equal(Δ[(k−2)2ᵏ], k·2ᵏ) = Certified{equal:false}`
  because `exp((k+1)ln 2)` and `exp(k ln 2)` don't combine. (Gosper works around
  this by certifying the reduced polynomial identity instead.)

## Why the render-string hack is insufficient

A `fold_exponential` at the `MultiPoly` level (mirroring `fold_radical`) would need,
for two `\0exp:` atoms in one monomial, to **sum their arguments** `A + B` and emit
`\0exp:<render(A+B)>`. But the monomial only stores the *rendered* argument string;
recovering `A` and `B` as expressions to add them requires parsing arbitrary
renders back to `CasExpr` — fragile and not general (`exp(sin x)` etc.).

## The sound design: an exponential generator in the monomial

Represent the exponential part of a monomial **structurally**, so multiplication
adds exponents. A monomial becomes:

```
Monomial {
    powers:  BTreeMap<String, u32>,   // ordinary atom powers (unchanged)
    exp_arg: ExpArg,                  // the argument A of a single factored exp(A)
}
```

where `ExpArg` is a canonical **linear form over atoms** — `BTreeMap<AtomKey,
Rational>` plus a rational constant — rich enough for the load-bearing cases
(`n·ln c`, polynomials-as-atoms, `α·x`) and closed under addition. (A full nested
`MultiPoly` argument would make `Monomial` mutually recursive with `MultiPoly`;
the linear-form restriction avoids that while covering ODE/recurrence/Gosper.)

Monomial multiplication: multiply `powers`, **add** the `exp_arg` linear forms.
`exp_arg = 0` ⇒ the factor is `e⁰ = 1` (drop). This makes `e^A·e^B = e^{A+B}` and
`e^A·e^{−A} = 1` fall out of the normal form automatically — the same way the
polynomial normal form already makes `x·x⁻¹`… (well, powers) work.

Normalization of `CasExpr::Unary(Exp, arg)`: normalize `arg`; if it is a linear
form over atoms/constants, install it in `exp_arg`; otherwise fall back to the
current opaque-atom behavior (so nothing regresses).

## Certification unlocked (all via the existing differentiate-and-check / plug-back)

- `dsolve_first_order_linear(p, q, var)` — integrating factor `μ = exp(∫p)`;
  `y = μ⁻¹(∫μq + C)`; certified by `equal(y' + p·y, q)`.
- `solve_recurrence(coeffs, inits, var)` — closed form `Σ Aᵢ rᵢⁿ` (rational `rᵢ`;
  `e^{n ln rᵢ}` representation); certified by substituting into the recurrence.
- Gosper geometric fragment certifies through the *full* telescoping identity, not
  just the reduced one.
- General `exp`/`log` simplification: `e^{x}·e^{−x} → 1`, `e^{x}·e^{y} → e^{x+y}`.

## Test plan (write first)

1. `equal(exp(x)·exp(-x), 1) = Certified{true}`; `equal(exp(x)·exp(y), exp(x+y))`.
2. `equal(exp(x)², exp(2x))`; `equal(exp(2x)/exp(x), exp(x))`.
3. Regression: every existing transcendental test (integration logs, series,
   Gosper) still passes — the opaque fallback must be exact for non-linear args.
4. Then the new capabilities above, each plug-back-certified.

## Risk / sequencing

This touches `Monomial`/`MultiPoly` — the trust core — so it lands **behind its own
test suite first**, with the opaque-atom path as the untouched fallback for any
argument that is not a linear form. It is the single highest-leverage substrate
step: it unlocks first-order ODEs, recurrences, the Gosper geometric certificate,
and general exp/log simplification together. Sequence it ahead of the assumptions
engine.
