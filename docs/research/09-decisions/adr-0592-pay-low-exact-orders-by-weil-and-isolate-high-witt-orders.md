# ADR-0592: Pay low exact orders by Weil and isolate high Witt orders

Status: accepted
Date: 2026-08-21
Index-summary: Pay exact character orders through ell over three log ell by Weil and restrict the factor-4ell endpoint hypothesis to the top Witt-order bands

## Context

ADR-0591 gave a sufficient endpoint premise by demanding a factor-`4ell`
saving separately in every exact-order, exact-conductor character family.  That
statement is deliberately uniform, but it makes the ordinary order-two
Artin--Schreier family look load-bearing.  Its character population is only
about `2^(j/2)`, rather than the `2^(j-1)` characters in a full conductor
layer.  Before importing power-trace or coding machinery, the endpoint ledger
must spend this exponential sparsity.

## Decision

Let `c=ceil(log2 ell)`, `a=ell-c-1`, and let `Q` be the largest power of two
with `3cQ<=ell`.  In the connected top window `a<=j<=ell`, pay every
exact-order layer of order at most `Q` by the proved summed individual-Weil
bound.  Require the ADR-0591 factor-`4ell` saving only when the exact character
order is greater than `Q`:

```text
4 ell |T_(j,s)(n)|
  <= #X_(j,s) (j-1) 2^ceil(n/2),       2^s > Q.
```

This weaker premise still proves both Lemire endpoints for every `ell>=200`.
The proof is elementary.  Put `R_m=sum_(j=1)^m (j-1)2^(j-1)`, so

```text
R_m=(m-2)2^m+2.
```

Writing `W=2^(ell+1)R_(a-1)` for the proved low-conductor envelope and `H`
for the ordinary full-character envelope in the top window, direct
substitution shows

```text
2^(2ell) - W - H/(4ell) >= 7*2^(2ell)/ell.             (1)
```

Indeed `ell<=2^c` gives

```text
W/2^(2ell) <= 1/2-(c+4)/(2ell)+2^(2-ell),
(W+H)/2^(2ell) = 2ell-4+2^(2-ell),
```

Collecting terms gives the stronger explicit margin

```text
[2^(2ell)-W-H/(4ell)]/2^(2ell)
 >= (4c+25)/(8ell) - (c+4)/(8ell^2) - 2^(2-ell)
 >= 7/ell.
```

Characters on `E_j` killed by `Q` number

```text
h_(j,Q)=2^(j-floor(j/Q)).
```

Consequently the complete unsaved low-order top contribution `L` satisfies

```text
L/2^(2ell)
 <= 2(c+2)ell / 2^floor(a/Q)
 < 7/ell.                                               (2)
```

For the last strict inequality, `Q<=ell/(3c)`.  Since
`3c(c+1)<2ell` for `ell>=200`, this gives

```text
floor(a/Q) >= 3c-2,
L/2^(2ell) <= 8(c+2)/ell^2 < 7/ell.
```

Equations (1)--(2) leave a strict endpoint margin.  Integer floors only
decrease the conditional high-order envelope.

Add `exact_order_high_order_saving_endpoint_implication` to replay the exact
integer ledger.  The focused test checks every integer endpoint from 200
through 1024 and additional dyadic boundary controls through 16384.

## Evidence

At `(ell,n)=(200,401)`, `Q=8`.  Of the 67 nonempty top-window exact-order
layers, 20 layers of orders 2, 4, or 8 are now discharged with no family
cancellation, and only 47 high-order layers retain a conditional estimate.
The same calculation applies to the even endpoint.  Focused native tests and
the fact-ledger validator fail closed on any lost strict inequality.

## Consequences

- Ordinary Artin--Schreier characters and the first low Witt layers are not
  the endpoint bottleneck.  Their individual-Weil bounds are sufficient.
- A proof effort should not spend time proving family cancellation for fixed
  exact order merely to satisfy the obsolete uniform premise.
- The remaining analytic obligation begins above `ell/(3ceil(log2 ell))` and
  has only `O(log log ell)` possible exact-order bands per conductor level.
  It is a genuinely high-Witt-order statement.
- This is a strict reduction of the open premise, not a proof of its
  high-order part.  The manuscript's fail-visible warning remains.
