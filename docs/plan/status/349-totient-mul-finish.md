# Lane: totient-mul-finish — `Nat.totient_mul_of_coprime`

<!-- plan-section: lane-status -->

**DONE (`totient-mul-finish`, 2026-08-30).** `Nat.totient_mul_of_coprime`
landed, axiom-free, admitted by the kernel on the **first attempt**. Three new
theorems in a new file `nat_prelude/totient_mul.rs`, **no new
`Definition`**, two new hand-curated ledger facts. `nat_prelude::` **192
passed, 0 failed** (188 baseline + 4 new tests, one of which was the coverage
assertion firing correctly before the names were registered). `clippy
-p axeyum-lean-kernel --all-targets -- -D warnings` clean; `cargo fmt --all
--check` clean; `validate-facts.py` **2222 facts checked, 0 errors**.

```text
Nat.totient_mul_of_coprime :
  ∀ m n, Eq (gcd m n) 1 → Eq (totient (mul m n)) (mul (totient m) (totient n))
```

Proved **by counting** — no prime factorization, no Euler product, no Bézout
witness, and no CRT *existence* over ℕ anywhere in the term.

## Where the coprimality hypothesis actually goes

This is the shape of the result, and it is why the file states three theorems
rather than one. Run before any Rust, and extended afterwards for the mirrors:

```sh
python3 scripts/tests/check-totient-mul-coprime-numerics.py
```

26 checks, each paired with a negative control the script asserts must
*genuinely* fail. Over every pair with `1 ≤ m,n ≤ 9`:

| step | needs coprimality? | measured |
| --- | --- | --- |
| `Nat.crtSelfMap_mapsInto` | **no** | holds at all 81 pairs, incl. all 26 non-coprime |
| pointwise `P x = V (g x)` | **no** | holds for all `x < 60` at all 81 pairs |
| Fubini via `countRange_product` | **no** | holds at all 26 non-coprime pairs |
| `Nat.crtSelfMap_injectiveOn` | **YES** | holds at **0 of 26** non-coprime pairs |
| the theorem itself | **YES** | fails at **26 of 26** non-coprime pairs |

So the entire hypothesis is carried by one obligation. A single fused lemma
would have made it look load-bearing everywhere and hidden which step pays for
it, which is exactly the confusion `301`'s traced plan fell into.

The map, with `N = mul n m` (`n` the block WIDTH, `m` the block COUNT — the
shape `countRange_product` factors) and `V y := band (R (div y n)) (S (mod y n))`:

```text
g x := add (mul n (mod x m)) (mod x n)

countRange P (mul m n)                        -- totient (m*n), by δ
  = countRange P (mul n m)                    -- mul_comm, on the BOUND only
  = countRange (V ∘ g) (mul n m)              -- countRange_congr, UNCONDITIONAL
  = countRange V (mul n m)                    -- countRange_permute, run SYMM
  = mul (countRange S n) (countRange R m)     -- countRange_product
  = mul (totient m) (totient n)               -- mul_comm
```

Detail moved to [`../notes/349-totient-mul-finish.md`](../notes/349-totient-mul-finish.md).

