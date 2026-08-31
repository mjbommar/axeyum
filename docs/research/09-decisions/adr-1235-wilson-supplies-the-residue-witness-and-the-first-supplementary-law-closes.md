# ADR-1235: Wilson's theorem supplies the residue witness, and the first supplementary law closes

Status: accepted
Date: 2026-08-31
Index-summary: The `p = 1 (mod 4)` half of the first supplementary law is
proved, with `m!` as the witness, by splitting Wilson's theorem at the half and
reversing the upper factor — no converse of Euler's criterion. With ADR-1230's
other half, the law is complete.

## Context

ADR-1230 landed the **non-residue** half of the first supplementary law of
quadratic reciprocity — for an odd prime `p = 2m+1` with `m` odd (i.e.
`p ≡ 3 (mod 4)`), `-1` is not a quadratic residue mod `p` — and was careful to
say the law was half landed and to refuse the word "closed".

Its handoff made two claims about the remaining half, and **both held**:

- The **converse of Euler's criterion is not needed.** Wilson's theorem gives
  `(p-1)! = (-1)^m (m!)^2`, so at even `m` the witness is `m!` outright. Its
  C5a/C5b rows verified that at 94 and 44 primes; this lane's C5–C9 re-derive
  it step by step and the numbers agree.
- The remaining blocker was **`InjectiveOn` and `MapsInto` for the reflection
  `k ↦ sub (pred m) k` on `[0,m)`**. Confirmed absent, and confirmed that
  `nat_prelude/count_range_reversal.rs` — which is about exactly that
  reflection — has nothing to reuse, because it runs its own well-founded
  induction rather than going through a permutation.

## Decision

Land the residue half. Three declarations, all axiom-free:

| declaration | statement |
| --- | --- |
| `Nat.sub_sub_self` | `∀ n k, Le k n → Eq Nat (sub n (sub n k)) k` |
| `Int.wilsonHalfSplit` | `∀ m, PrimeCond (succ (mul 2 m)) → ModEq (ofNat (succ (mul 2 m))) (mul (factorial m) (mul (pow (neg one) m) (factorial m))) (neg one)` |
| `Int.firstSupplementaryLawResidue` | `∀ m, PrimeCond (succ (mul 2 m)) → Nat.Even m → IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one)` |

`nat_prelude/order.rs`, `int_prelude/first_supplementary_residue.rs`. Facts
`F:nat-sub-sub-self`, `F:int-wilsonhalfsplit`,
`F:int-firstsupplementarylawresidue`.

**With `Int.firstSupplementaryLawNotResidue` (ADR-1230), the first
supplementary law is complete** — and it is complete in exactly this sense and
no stronger one: the two halves are separate implications covering the two
residue classes of an odd prime mod 4, so between them they decide `-1`'s
quadratic-residue-hood for every odd prime. **No single declaration in this
prelude carries the biconditional**, and neither fact alone decides anything
about the other class. Say "both halves are proved", not "the biconditional is
declared".

## The route, and what it needed

```text
  (p-1)! = m! · ∏_{j=m+1}^{2m} j                -- prodRange_split at (m, m)
         = m! · ∏_{k<m} (2m - k)                -- prodRange_permute at the reflection
         ≡ m! · ∏_{k<m} (-1)·(k+1)     [p]      -- modEq_prodRange_lt; 2m-k + (k+1) = p
         = m! · ((-1)^m · m!)                   -- prodRange_scaledIndexEqPowMulFactorial
```

`Int.wilson` closes the left side at `-1`; `Int.pow_neg_one_of_even` closes the
sign at even `m`; `int_exists_intro` at witness `Int.factorial m` closes the
residue.

Every step except the reflection's two permutation predicates already existed,
including `Int.prodRange_split`, which ADR-1230's lane landed for exactly this.

### The bounded involution, and the helper that was pointed at wrongly

ADR-1230's handoff said to promote `nat_prelude/transposition.rs`'s private
`injective_of_involutive` rather than re-derive it. **That helper does not
apply.** It is `NatDev`-typed and its hypothesis is an *unbounded* involution
law `∀ x, t (t x) = x`, and the reflection is **not** a global involution:
`Nat.sub` truncates, so `sub 3 (sub 3 5) = 3`, not `5`. The same objection
rules out the already-public `Nat.conjugate_injective`.

What does apply, and was reused verbatim, is `int_prelude/wilson.rs`'s private
`injective_of_involutive_local` — same three-line argument, `IntDev`-typed, and
taking exactly the **bounded** law `∀ k, Lt k n → σ (σ k) = k`. It was written
generic over `σ` for `Nat.inverseIndex` and needed only `pub(super)`.

So the handoff's instruction — *promote, do not re-derive* — was right, and the
helper it named was the wrong one. Same file family, one prelude over.

`Nat.sub_sub_self` is the one genuinely new lemma. It has no induction of its
own (`sub_add_cancel`, one rewrite of the outer `n`, `add_sub_cancel_left`) and
its `Le k n` hypothesis is not cosmetic — the unbounded form is false, which is
what makes the bounded involution the only route. `MapsInto` does not use it at
all: it is `sub_le` then `sub_lt`, two lines.

### Index arithmetic

The pointwise congruence needs, in `Nat` and for `k < m`,
`succ k + succ (m + σ k) = succ (2m)`. `Nat.add` recurses on its RIGHT
argument, so `add x (succ y)` iota-reduces and exactly **one** `succ_add` is
needed; the rest is `add_comm`/`add_assoc`, `sub_add_cancel` (which turns
`σ k + k` into `pred m`) and `succ_pred_of_pos`.

`0 < m` is never a hypothesis of anything here — it is derived from `k < m`,
which is in hand wherever it is needed. So the `m = 0` boundary is excluded by
primality alone (`p` would be `1`), and the theorem needs no side condition of
its own.

Lifting to `ℤ` needed **no `ofNat_add` lemma**: `Int.add (ofNat a) (ofNat b)`
is definitionally `ofNat (add a b)`, so `nat_eq_to_int` carries the whole
identity across. `Int.modulus_modEq_zero` then gives `p ≡ 0 [p]`
unconditionally and `Int.modEq_add_left_cancel` peels the shared `ofNat (k+1)`
off both sides. This is the "several carrier bridges turn out free" pattern.

## Numeric verification

Re-runnable, and it fails when the thing it checks is false:

```sh
python3 docs/research/09-decisions/adr-1235-first-supplementary-residue-checks.py
```

Thirteen claims — one per step the Rust proof actually takes, in order — each
paired with a mutated form that must be refuted; exit 1 if any claim fails or
any mutation survives. Current run: 0 failures on every row, every control
refuted. ADR-1230's own script was re-run rather than inherited: also PASS.

The rows that matter most are C1 (the involution law, refuted at the dropped
bound), C4 (the pointwise index identity, refuted one past the range), C7 (the
congruence WITHOUT the reflection, refuted at every prime), and C9 (the
assembly, refuted when extended to odd `m`).

## What was measured

Nine mutations, none surviving, in **three** columns. The third is the one this
lane was told to design for, and it is the largest.

| mutation | outcome |
| --- | --- |
| M1 residue half restated at `Nat.Odd m` (sign lemma swapped to match) | **B**: kernel rejected, and the statement is FALSE |
| M2 `wilsonHalfSplit` restated without the `(-1)^m` factor | **B**: kernel rejected, and the statement is FALSE |
| M3 `succ_pred_of_pos` used without the `symm` | **A**: kernel rejected, statement unchanged |
| M4 reflection off by one (`sub m k`) | **A**: kernel rejected, statement unchanged |
| M5 pointwise factor scaled by `+1` instead of `-1` | **A**: kernel rejected, statement unchanged |
| M6 residue half concluded at `one`, proved by `is_quadratic_residue_one` | **C**: kernel ADMITTED, statement TRUE, not the law |
| M7 residue half given an extra unused `Nat.Odd m` hypothesis | **C**: kernel ADMITTED, statement vacuously TRUE, not the law |
| M8 residue half concluded at `ofNat (2m)`, transported by `isQuadraticResidue_of_modEq` | **C**: kernel ADMITTED, statement TRUE, not the law |
| M9 the M5 control's `!def_eq` inverted | the test FAILS — the control is not vacuous |

**Column B is distinguishable from column A, and the distinction is not
cosmetic.** In both the kernel rejects, but in A the mutation broke a proof
step and the statement is still true, while in B the mutated *statement is
false* — and that is exhibited independently rather than inferred from the
rejection. M1's falsity is refuted **in-kernel**: with `Odd m` the same
conclusion composes with `Int.firstSupplementaryLawNotResidue` to give `False`,
and the test asserts exactly that. M2's is refuted by the kernel *computing*
both sides' `Int.emod` at `m = 3, p = 7` to `6` and `1` — with the `m = 2,
p = 5` row beside it, where the unsigned form DOES hold, so the control is
visibly not vacuous.

**M8 is ADR-1230's M5, mirrored, and it behaved identically.** `ofNat (2m)` is
`-1`'s canonical representative mod `p`, so concluding there yields a statement
the kernel admits and which is true — and is not the first supplementary law,
because that law is about `-1`. Nothing in the axiom footprint, the prelude
build, or `every_int_declaration_is_checked_and_axiom_free` sees the
difference; only the test's symbolic shape check does. M6 and M7 are two more
of the same shape found while looking for it, and M7 is the worse one, because
a vacuously-true theorem passes every check this repository has except a shape
comparison of its full type.

M9 exists because a control that cannot fail is worse than no control:
inverting the `!def_eq` makes the test fail, so the two propositions really are
distinguishable and the assertion measures something.

### What the controls do NOT catch

- **Hypothesis satisfiability.** As in ADR-1230, the test never constructs a
  `PrimeCond` proof. A mutation making `PrimeCond p ∧ Even m` unsatisfiable
  would leave a vacuously-true theorem the shape check still passes — M7 is
  caught only because it changes the *arity*, not because anything here can see
  vacuity. The hypotheses are satisfiable (`m = 2` gives `p = 5`) and the
  numeric script's C9/C10 rows exercise the 44 such primes below 500, but that
  is evidence from outside the kernel.
- **Hiding place 2.** Every helper in
  `int_prelude/first_supplementary_residue.rs` is private —
  `reflect_involutive`, `reflect_maps_into`, `pos_of_lt`, `le_pred_of_lt`,
  `index_sum_eq_p`, `pointwise_modeq` — so
  `scripts/check-shape-duplicates.py` structurally cannot see a later lane
  re-deriving any of them. `pos_of_lt` and `le_pred_of_lt` are the ones most
  likely to be rebuilt; both are two lines and neither is worth a declaration,
  but the blindness is real and is recorded here because nothing else records
  it.
- **Whether `Int.factorial m` is the *smallest* witness, or unique.** The
  statement is an existential and says nothing about which `x` was used; the
  witness is visible only in `wilsonHalfSplit`'s type, which names
  `Int.factorial m` explicitly, and in the proof term.

## Two defects, and how they were found

Both were found by a throwaway `#[cfg(test)] mod debug_probe` that closed each
intermediate over a free `m` and ran `Kernel::infer` on it, printing one line
per step. It located both in **one run**; a bisect would have been serial.

- `Nat.sub_sub_self` was declared in `order.rs` **before** the
  `Nat.add_sub_cancel_left` it consumes. Symptom: `UnknownConst { name:
  NameId(165) }` across **all 297** `nat_prelude::` tests and all 62
  `int_prelude::` ones, naming neither lemma. This is the "one bad declaration
  poisons the shared prelude build" shape with a name-resolution cause rather
  than a type one.
- `index_sum_eq_p` used `Nat.succ_pred_of_pos` in the wrong direction. Its
  statement is `Lt zero n → Eq n (succ (pred n))`, **not** the reverse; one
  `d.symm` fixes it. Symptom: a bare `TypeMismatch` at the whole prelude build,
  several rewrites away from the arithmetic.

The probe was removed afterwards. It is recorded because the retrieval-shaped
lesson generalises: **a helper's stated DIRECTION is not predictable from its
name**, and `succ_pred_of_pos` reads as if it concluded `succ (pred n) = n`.

## Consequences

- Say **"both halves of the first supplementary law are proved"**, and if you
  say the law is complete, say in the same breath that it is two implications
  and not one declared biconditional.
- `Int.wilsonHalfSplit` is the reusable piece and is stated for **both**
  parities on purpose. The odd-`m` reading — `(m!)^2 ≡ 1 [p]` when
  `p ≡ 3 (mod 4)` — is one `pow_neg_one_of_odd` away and is not landed here.
- `Nat.sub_sub_self` is the general reflection-is-an-involution lemma; anything
  reversing a `prodRange`, `sumRange` or `countRange` over `[0,n)` should reach
  for it plus `wilson.rs`'s `injective_of_involutive_local` rather than
  rebuilding either.
- `wilson::injective_of_involutive_local`, `prod::compose` and
  `first_supplementary::pos_of_nat_succ` are now `pub(super)`. They were
  private and identical to what this module needed; extracting beat
  re-deriving, again.
