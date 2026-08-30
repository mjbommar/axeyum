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

`countRange S n` and `countRange R m` are `totient n` and `totient m` **on the
nose** — `R` and `S` are built by the same recipe as `totient`'s own
predicate — so nothing bridges them.

## Which of `344`'s three remaining pieces were real

All three were real. Two were cheaper than described and one needed machinery
the handoff did not mention.

1. **`MapsInto` — real, but ONE lemma, not a chain.** `344` described a
   four-step inequality (`mod x m < m`, `mod x n < n`,
   `(x mod m)*n + (x mod n) < ((x mod m)+1)*n ≤ m*n`). That is precisely
   `Nat.mul_succ_add_lt_of_le_of_lt` (`order.rs`), which already existed —
   the "flatten a row-major `(block, offset)` index" bound. With
   `Nat.mod_lt` supplying both hypotheses (the first through `le_of_lt_succ`)
   the whole proof is one `d.lemma` call, and stated at PREDECESSORS it needs
   **no hypothesis at all**.

2. **`InjectiveOn` — real, and every ingredient `344` named exists and works.
   One simplification.** `344` named `div_mod_same_remainder_mod_eq` for the
   forward direction and `div_mod_remainder_eq_of_mod_eq` for the reverse.
   `Nat.mod_eq_iff_div_mod_remainder_eq` is the **`Iff`** covering both, takes
   `Nat.div_mod_exec`'s executable witnesses directly, and is used in both
   directions here — one lemma instead of two.

   `344`'s two other claims about this step are confirmed exactly:
   `nat_prelude/crt.rs` (the **Nat**-native one) transports directly, and **no
   Bézout witness and no CRT existence over ℕ is needed.**

3. **Assembly — real, with two corrections that cost attempts if inherited.**

   - **`countRange_permute` must be run BACKWARDS.** It produces
     `countRange V N = countRange (V ∘ g) N`; the chain needs the other
     direction, so it is applied to `V` and then `symm`'d. `344`'s step (2)
     reads as if it applies forwards to `P`.
   - **A `Bool`-valued conjunction had to be built, and `344` does not mention
     it.** `countRange_congr` needs a pointwise `Eq Bool`, so `V` must be a
     concrete `Bool` function; this prelude exposes none (`finite_set.rs`'s
     `bool_select_bool` is private). The local `band` is the only genuinely new
     machinery in the file, and it is deliberately strict in its **first**
     argument so that `band false _ ≡ false` and `band true b ≡ b` hold by
     ι-reduction — which is what discharges `countRange_product`'s two
     per-block hypotheses with no lemma at all.

   One smaller correction: `344` writes the map as
   `add (mul (mod x m) n) (mod x n)`. `div_mod_block` reads back
   `add (mul n a) b`, so putting `n` on the **left** of the product removes a
   `mul_comm` from every use of it.

## Two things the term does that are worth copying

- **Predecessors, not positivity hypotheses.** Both self-map facts are stated
  at `succ mp` / `succ np`. Three things need the successor form
  *syntactically*: `mul_succ_add_lt_of_le_of_lt`, `div_mod_exec` (which takes
  the divisor's **predecessor**), and — the one that saved real work —
  `mul (succ np) (succ mp)` is definitionally `succ (add (mul (succ np) mp) np)`
  by two ι-steps, so `div_mod_exec` applies at the **product** modulus with no
  arithmetic lemma. The main theorem splits both arguments once at the top.
- **No new `Definition`.** `g`, `R`, `S` and `V` are bare lambdas, so nothing
  here owes an evaluation test — the kernel cannot tell a definition it is
  wrong. The `n = 0` boundary is `Eq.refl zero` for free (`Nat.mul` recurses
  RIGHT); `m = 0` is not free and needs `Nat.zero_mul` twice.

## Verification

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib nat_prelude::`
  — **192 passed, 0 failed**, finished in 4.57 s.
- `python3 scripts/tests/check-totient-mul-coprime-numerics.py` — 26 checks,
  every negative control asserted to fail.
- Three Rust tests, each aimed at a different defect class:
  - `totient_mul_of_coprime_computes_at_coprime_pairs_with_a_non_coprime_control`
    — CLOSED instances at (2,3) and (3,4) with the hypothesis supplied by
    `coprime_succ_self` (a real proof, not a `refl`), every count required to
    COMPUTE, and a control at `m = n = 2` where `gcd 2 2` does not reduce to 1
    **and** the conclusion is false (2 against 1, `!def_eq`).
  - `the_totient_multiplicativity_family_applies_at_free_variables` — all
    three at genuinely free variables via `LocalContext`/`infer_in`, plus a
    `!def_eq` against the TRANSPOSED factor order, since
    `totient m * totient n` and its transpose are different theorems that both
    type-check at numerals.
  - `the_crt_self_map_permutes_a_coprime_block_and_collides_on_a_non_coprime_one`
    — EVALUATION, not type-checking, because the map is a bare lambda: the six
    images at (2,3) are identified individually and required pairwise
    distinct, and at (2,2) `g 0 = g 2 = 0` with real proofs that both inputs
    are below the bound.
- Two ledger facts, `F:nat-totient-mul-of-coprime` and
  `F:nat-crt-self-map-injective-on`, six `checker_command`s **run** (all
  exit 0) and each grep pin verified to DISCRIMINATE by mutation — the
  transposed-factor pin and an absent-name pin both exit 1.

## The two `ml430` mirrors: NOT closed, and precisely why

Both are `partition: development` in `artifacts/autogenesis/nursery-v2-extension.json`
(checked before touching them — neither is held-out). Both stay **open**, and
`316`'s sizing is confirmed rather than overturned.

- `F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7` —
  `∀ a b, φ(gcd a b) * φ(a*b) = φ a * φ b * gcd a b`. **At a coprime pair this
  collapses to exactly the landed theorem** (`φ(1) = 1`, trailing `gcd = 1`),
  so that half is done. At the **53** non-coprime pairs with `1 ≤ a,b ≤ 12` it
  does not collapse and is strictly stronger — checks 21–23 of the numerics
  script.
- `F:ml430-nat-totient-dvd-of-dvd-9622e44a` — `∀ a b, a ∣ b → φ a ∣ φ b`. The
  divisibility hypothesis is load-bearing (it fails at 69 non-dividing pairs
  in the same range), and nothing in the coprime case gives it.

**Neither follows from `totient_mul_of_coprime`.** Both need the non-coprime
formula, which needs a totient value at prime powers plus a product over a
factorization. That framework does not exist here, measured rather than
assumed:

```sh
grep -c 'totient' crates/axeyum-lean-kernel/src/nat_prelude/factorization.rs   # 0
grep -rn 'totient_prime_pow\|totient_pow\|totient_factorization' \
     crates/axeyum-lean-kernel/src/nat_prelude/                                # empty
grep -oE 'pub totient[a-z_]*: NameId' crates/axeyum-lean-kernel/src/nat_prelude.rs
#   -> 7 rows: the positive control, so the two zeros above are real negatives
```

The concrete next rungs, in order: `φ(p^k) = p^k - p^(k-1)` for prime `p`, then
the factorization product `φ(n) = ∏ φ(p_i^{k_i})` (which is where
`totient_mul_of_coprime` becomes the induction step), then either mirror falls
out. Do not size that as an extension of this lane.

## One tooling finding

`nat_theorem_inventory` **consumes only ONE name argument and reports on the
LAST one** — confirmed in both orders (`totient_mul_of_coprime crtSelfMap`
printed the two `crtSelfMap` rows; `crtSelfMap totient_mul_of_coprime` printed
the one totient row). A two-name call looks like a clean result while silently
answering about one of them. Same shape as `CLAUDE.md`'s documented
`theorem_dependency_inventory` trap, opposite end of the argument list. Both
new fact checkers pass exactly one name.

Related, and it corrected this lane: a `"kernel_theorem": "Nat.mul_comm"` grep
of the ledger reported that lemma unregistered. It is registered.
`scripts/check-fact-depends-derived.py --fix` derives `depends_on` from the
**proof term** and found 11 edges I had missed across the two facts — use it
rather than reading your own source for dependencies.
