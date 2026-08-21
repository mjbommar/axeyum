# ADR-0591: Reconstruct exact-order traces by power-subgroup orthogonality

Status: accepted
Date: 2026-08-21
Index-summary: Convert every exact-order Hayes trace into four ordinary power-subgroup populations and price a factor-4ell order-layer saving that closes the endpoint

## Context

ADR-0534 groups primitive Hayes characters first by cyclotomic Galois orbit
and then by exact character order.  This retains substantial cancellation, but
its implementation still evaluates every character.  To turn the observed
order layers into a theorem target, their arithmetic content must be stated in
class space and their required endpoint strength must be priced before another
finite envelope is pursued.

## Decision

Let `E_j=(1+x GF(2)[x])/(x^(j+1))`, let `pi:E_j->E_(j-1)`, and let
`N_n(g)` be the degree-`n` Mangoldt population of class `g`.  For `s>=0` put

```text
H_(j,s) = {chi in E_j^dual : chi^(2^s)=1},
h_(j,s) = |H_(j,s)| = 2^(j-floor(j/2^s)),
P_(j,s) = sum_(g in 2^s E_j) N_n(g).
```

Finite-group orthogonality gives

```text
sum_(chi in H_(j,s)) chi(g) = h_(j,s) 1_(g in 2^s E_j).
```

Taking one difference in `s` for exact order and one difference in `j` for
exact conductor proves the exact spatial formula

```text
T_(j,s)(n)
 = h_(j,s)P_(j,s) - h_(j,s-1)P_(j,s-1)
 - h_(j-1,s)P_(j-1,s) + h_(j-1,s-1)P_(j-1,s-1).
```

Here `P_(j-1,s)` is evaluated on `pi(g)`: summing the fine populations over
that condition recovers the ordinary coarse population.  Raising a principal
unit to `2^s` substitutes `x->x^(2^s)`.  Hence, if `2^s` divides `j`, the new
coefficient is allowed and

```text
h_(j,s)P_(j,s)-h_(j-1,s)P_(j-1,s)=0.
```

Otherwise the new coefficient is forced to zero and the same cumulative
trace is

```text
h_(j-1,s) (2P_(j,s)-P_(j-1,s)).
```

Add `hayes_exact_order_spatial_trace_report` as an independent class-space
reconstruction.  It does not call the cyclotomic orbit calculation.  Add two
symbolic endpoint ledgers:

1. the deliberately strong diagnostic
   `|T_(j,s)| <= j^2(j-1)2^ceil(n/2)`;
2. the load-bearing weaker premise

```text
4 ell |T_(j,s)(n)|
  <= #X_(j,s) (j-1) 2^ceil(n/2),
```

where `#X_(j,s)` is the exact number of conductor-`j`, order-`2^s`
characters.  The second premise saves only a factor `4ell` over summing the
individual Weil bound.  The exact ledger proves it is sufficient for both
Lemire endpoints for every `ell>=200`, after the existing degree-400 handoff.

## Evidence

The focused native test compares every exact-order spatial trace, its total
character population, and the reconstructed conductor trace with the
independent two-prime cyclotomic calculation at both endpoint parities through
level 12.  It also checks the closed count
`h_(j,s)=2^(j-floor(j/2^s))` against the product of Witt cyclic factors.

The symbolic endpoint test checks both implications for both parities at every
`200<=ell<=1024`.  At `(ell,n)=(200,401)`, the top window has 67 nonempty
order layers.  A uniform coefficient as large as
`39000171862109468579481394744175882465620218685402070686` would still fit
the triangle ledger, so the `j^2` experiment is intentionally far stronger
than the endpoint needs.

Fleet rows are falsification evidence only.  The strong `j^2` envelope
survives both parities through level 22 and is refuted at the level-23 even
endpoint: its required coefficient is 710 against allowance 529.  This does
not refute the much weaker character-count-weighted factor-`4ell` premise.
All-feature CAS `lib`/`bins`/`tests` Clippy and formatting pass; untracked
reviewer examples remain outside the owned Clippy scope.

## Consequences

- Exact character order is no longer merely a cyclotomic representation.  It
  is a four-term integer identity among sparse prescribed-coefficient
  Mangoldt populations.
- The nonempty order-layer count at conductor `j` is exactly
  `ceil(log2(j+1))-v_2(j)`, only logarithmic in `j`.
- A proof need not establish the strong finite `j^2` envelope.  A factor
  `4ell` average saving inside every exact-order family already closes the
  endpoint without cancellation between order layers.
- Neither the spatial identity nor the implication proves that saving.  The
  manuscript's `(REL)` warning remains, and no Lemire theorem credit is
  granted.
