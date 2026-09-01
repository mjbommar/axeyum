# Lane `det-multiplicativity` — `det (A·B) = det A · det B`

Status: IN PROGRESS (early commit, nothing landed yet).

Base: merged local `main` at `3be794a8e` (origin/main lagged at `46bc65cc4`).

## Route chosen (to be verified, not inherited)

ADR-1310 step 4. The Cauchy–Binet / multilinearity route:

1. **Row multilinearity** — `det` of a matrix with row `t` replaced by
   `λc. sumRange (λk. coef k c) n` equals `sumRange (λk. det (row t := coef k)) n`.
   Built on `Rat.det_row_expansion` + the row-`t` minor's independence of row
   `t`'s value (the machinery already inside `row_add_split`).
2. **n-fold expansion** of `det (A·B)` into a sum over all maps `[0,n) → [0,n)`.
3. **The selection lemma** `det (B∘g) n = det (matId∘g) n * det B n`.
4. Assembly at `B := matId` using `matMulIdRight`.

## Early assessment of the wall

(3) is where ADR-1310's warning about `leibniz`-agrees-with-`det` really lands.
The route that avoids permutation *decomposition* is an induction on `k` with

    P(k) : ∀ σ, InjectiveOn σ n → MapsInto σ n → (∀ i, k ≤ i → σ i = i)
             → det (B∘σ) n = det (matId∘σ) n * det B n

whose step composes `σ` with the transposition `(k, σ⁻¹ k)` — the same
pigeonhole skeleton `Int.prodRange_permute` uses, with a sign tracked by
`Rat.det_row_swap`. Written down here before building anything, so a later
lane can judge it against what actually landed.
