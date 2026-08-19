# Notes: creal-field

Detail kept out of [`../status/65-creal-field.md`](../status/65-creal-field.md)
so the lane block stays inside the per-lane ceiling (ADR-0507). The decision
itself is
[ADR-0510](../../research/09-decisions/adr-0510-the-real-inverse-is-partial-and-its-modulus-is-data.md).

## What was actually missing, and it was not on any list

**ℚ was not a field.** `Rat.inv` has existed since the rational prelude was
written — a three-way dispatch on the numerator's sign, `inv 0 = 0` by the usual
total convention — and *nothing anywhere said it inverted anything*. `Rat.div`
is defined through it and was equally unconstrained. Every plan for `CReal.inv`
assumed the rational inverse was usable; it was not, and this is the second time
in this development that a prerequisite turned out to be one level down (the
first was `Rat.bounds_num` under `CReal.bound`).

The proof is the only one in either field module that touches the
representation, because `Rat.inv q` is **stuck** until `Rat.num q` is in
constructor form. Two of the three branches cost nothing:

- `num q = ofNat 0` — `eq_zero_of_num_zero` gives `q = 0`, `lt_irrefl` closes;
- `num q = negSucc m` — `Int.lt Int.zero (negSucc m)` **ι-reduces to `False`**,
  `Int.lt` being a four-case definition and this the mixed-constructor case. No
  lemma at all, just `False.rec`. This was the branch expected to need a sign
  discriminator and it needed nothing.

The dispatch is not transcribed into the proof: `rat_prelude::defs::inv_body` is
factored out of the definition, `Rat.inv q` **is** `inv_body q (num q)`, and the
case split's motive names the same construction. If the definition changes, the
proof fails at the kernel rather than proving something about a stale copy.

Everything after that is `group.rs`'s discipline — derived from
`mul_inv_cancel` and the 22 laws alone, never a numerator — so each lemma is a
theorem of *ordered fields*: `inv_pos`, `sub_mul`, `mul_inv_sub_one`,
`inv_sub_inv`, `inv_le_of_pos_le`. `sub_mul` came out free: it is `mul_sub_mul`
(already proved for `CReal.mul`) with its first summand `a·(w − w)` collapsed.

## The measurement that changed the design

The obvious reading of "the inverse needs apartness, and apartness is a `Prop`"
is that a `Prop` hypothesis blocks a `Type`-valued definition. **That reading is
wrong**, and it was in this lane's own module doc for one commit.

A function may *take* a `Prop` argument and return a `Type`. What it may not do
is *branch* on one. So:

- `inv : (x : CReal) → Apart x zero → CReal` is **not** definable — `Apart` is
  an `Or`, and choosing which of the two reciprocals to compute eliminates a
  disjunction into `Type`. This is exactly why CoRN carries apartness in
  `CProp`, a `Type`-valued logic.
- `inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` **is** definable, with
  `PosBound x k := le (ofRat (natDivSucc 1 k)) x`: no disjunction, the
  representative depends on `k` alone, and the proof only ever discharges
  `CReal.mk`'s `Prop`-valued regularity field.

So the thing that must be data is the **modulus**, not the proof — and
`pos_bound_of_lt` says the modulus always exists while being unextractable,
which is the whole constructive content in one theorem.

## `CReal.inv` is not built. Here is the design and what it costs

The construction is fixed; the remaining work is index arithmetic. Write
`c := natDivSucc 1 k` (the hypothesis' bound) and `L := natDivSucc 1 (2k+1)`, so
`L + L = c` by `natDivSucc_add` + `natDivSucc_halve`.

**The sampling index is `j(n) := (C+1)·n + C` with `C + 1 := (4k+4)·(k+2)`,** and
the whole trick is that this one index reads back **two** ways through the
existing `Rat.natDivSucc_le_scaled`, so that
`Rat.natDivSucc` still never has to be antitone in its index — the ~250-line
lemma this development has now dodged four times:

1. *A constant lower bound.* `j(n) + 1 = ((k+2)(n+1))·(4k+4)`, so
   `j(n) = (e+1)·(4k+3) + e` with `e := (k+2)·n + (k+1)` — no ℕ-subtraction.
   Hence `2/(j(n)+1) ≤ 2/(4k+4) = L` by `natDivSucc_le_scaled` at numerator 2
   plus `natDivSucc_scale`. With `PosBound` at index `j(n)` and `c = L + L`,
   that gives `L ≤ x_{j(n)}` for **every** `n`.
2. *A shrinking bound.* `j(n) = (C+1)n + C` directly, so
   `K/(j(n)+1) ≤ (C+1)/(j(n)+1) = 1/(n+1)` by `natDivSucc_le_add_left` (monotone
   in the numerator, additively) then `natDivSucc_scale`, for any `K ≤ C+1`. The
   `K` the regularity estimate produces is `B²` with `B := natDivSucc (2k+2) 0`,
   and `C + 1 = B² + (4k+4)` exactly, which is why the factor `(k+2)` is there.

Then `invSeq x k n := Rat.inv (seq x (j(n)))`, and:

- **regularity** is `inv_sub_inv` (the difference of two reciprocals is the
  difference of their arguments scaled by both), the regularity of `x`, and
  `bounds_mul` twice, fused by `natDivSucc_mul` and read back by (2);
- **`mul_inv_cancel`** over ℝ is `mul_inv_sub_one` at the product's own sampling
  index `J`, and it must close through `Equiv.of_bounded` rather than the exact
  estimate, because the product's shift depends on `CReal.bound` of the two
  factors — opaque `natAbs` projections — so no relation between it and `2B` is
  available. `of_bounded` does not care: the constant is free.

**Costed at ~1,200–1,500 lines of proof script**, of which the genuinely new
part is the ℕ side: two degree-2 polynomial identities in `k` and `n`
(`(C+1)n + C = (e+1)(4k+3) + e` and `(4k+4)(k+2) = (2k+2)² + (4k+4)`). Those are
the same kind of obligation as `Rat.nat_index_compose`, and they are the reason
this is a separate slice rather than one more commit.

Two ℚ lemmas are still needed and are not built: `L⁻¹ = B` (from `L·B = 1` via
`natDivSucc_mul`/`natDivSucc_scale`, plus `natDivSucc 1 0 = Rat.one`), and
`0 ≤ x⁻¹` at the samples, which is `inv_pos` + `le_of_lt`.

## `CReal.mul_pos`, and why it is not one of the 22

Positivity is closed under multiplication over the constructed reals. The 22
give `mul_nonneg` (`0 ≤ x → 0 ≤ y → 0 ≤ x·y`) and **the strict version does not
follow from it by any rearrangement** — `0 ≤ x·y` holds of the zero product too.

Over ℚ it is a *field* lemma: were `a·b ≤ 0`, scaling by the nonnegative `a⁻¹`
would give `b = a⁻¹·(a·b) ≤ a⁻¹·0 = 0`, contradicting `0 < b`. So `Rat.mul_pos`
goes through `Rat.inv_pos`, which is why it lands in the field module and not in
`laws`. Over ℝ it needs no estimate at all: `CReal.lt` carries rational gaps
`q₁ ≤ x` and `q₂ ≤ y`, two applications of `mul_le_mul_of_nonneg_left` give
`q₁·q₂ ≤ x·y`, `CReal.ofRat_mul` says the embedded product is the rational
product, and `Rat.mul_pos` makes it positive.

It is also the first place the `Exists` in `CReal.lt` is opened twice in one
proof — and it works precisely because the *target* is a `Prop`. The
elimination an inverse would need lands in `Type`, and that asymmetry is the
same one `pos_bound_of_lt` records.

## What is NOT ordered-field structure here, and why

- **No inverse for `x < 0`.** `Rat.mul_inv_cancel`'s hypothesis is `0 < q`; the
  negative branch of `Rat.inv` is one case split away and unneeded. Over ℝ the
  general `x # 0` case cannot be reduced to the positive one by *branching* on
  the disjunction (§ above); it has to be `inv (neg x)` under a separate
  hypothesis, or the caller picks the sign.
- **No cotransitivity of `lt`** (`x < y → ∀ z, x < z ∨ z < y`) — the law that
  most sharply separates real apartness from mere inequality, and the one that
  makes `Apart` usable for case analysis in proofs. It *is* constructively
  provable: from the gap `q`, compute `r` with `8r < q`, compare `z_N` against
  `x_N + 4r` on the proved `Rat.le_or_lt`, and both branches close. Cost: two
  full estimates of `le_add_of_nonneg`'s size plus the index computation,
  ~400 lines.
- **No `apart_mul`** (`x # 0 → y # 0 → x·y # 0`, the constructive field's
  nonzero-product axiom). `CReal.mul_pos` is one of its four sign cases; the
  other three need `lt x zero ↔ lt zero (neg x)` and `(−x)·(−y) ≈ x·y` over
  `Equiv`, neither of which exists yet. ~300 lines.
- **No `abs`, `max`, `min`.** These need no completeness and are reachable, and
  the obstacle a reader expects — that `max` needs a decision and `Rat.le_or_lt`
  is `Prop`-valued, so it cannot be case-analysed into `Type` — is avoidable:
  `Rat.abs q := normalize (ofNat (natAbs (num q))) (den q) (den_pos q)` is a
  *definition* on the representation, and `max a b` follows from it. What it
  then costs is one ℚ lemma with a four-way sign split
  (`|a| − |b| ≤ |a − b|`, in the `−b ≤ a ∧ a ≤ b` encoding), after which
  `CReal.abs` is pointwise and its regularity is immediate. ~500 lines.
- **No `sqrt`, no completeness, no supremum.** Each is its own ADR. ℂ's `abs`
  needs `sqrt` needs completeness, so ADR-0508's gap is untouched by this lane.
- **No Markov's principle in any disguise.** `¬(x ≈ 0) → x # 0` is not proved,
  not assumed, not used — and `not_equiv_of_apart` is stated one-way so that a
  later reader cannot mistake the available direction for an equivalence.

## Guards, measured rather than asserted

- Deleting `declare_apart_zero_one`: **2 tests die** (the declaration inventory
  and the statement test), 353 pass, and the witness example flips to exit 1
  with the matching `FAIL:` line. `apart_symm`, `apart_irrefl` and
  `apart_congr` all hold — footprint-free — of the relation that separates
  nothing, which is also the relation an inverse would be vacuously definable
  over.
- Deleting `declare_no_total_inverse`: **2 tests die**, 353 pass, example exit 1
  with its own `FAIL:` line.
- Negative control, ℝ: the identical `no_total_inverse` script pointed at
  `∀ x, x · f x ≈ 0` — **false**, take `f := fun _ => zero` — is REFUSED by the
  kernel.
- Negative control, ℚ: `Rat.inv (2/1)` reduces to `1/2` and `Eq.refl` is
  accepted; the identical script pointed at `(2/1)⁻¹ = 2/1` is REFUSED. This is
  the row that pins the *operation*: `mul_inv_cancel`'s hypothesis is `0 < q`,
  so it says nothing about `Rat.inv` off the positives and a "reciprocal"
  agreeing with the real one only there would satisfy it.
- Statements are asserted **verbatim** (rendered types), never by footprint: an
  empty footprint on a theorem named `mul_inv_cancel` that says something weaker
  would pass a footprint check.

## Numbers

- `-p axeyum-lean-kernel --lib`: **352 → 363** tests, all passing.
- `CReal` declarations: **58 → 71**; `Rat` gains 9.
- `nat_axiom_inventory --include-constructed`: `rat` and `creal` both
  `axiom=0 opaque=0 quotient=0 total_trusted=0`, unchanged.
- `gen-lean-axiom-ledger.py --check`: `total=30 … creal=0 rat=0 real=30`,
  unchanged — no field law is one of the 22, so no count moves.
- A full `CReal` build type-checks in ~45 s (debug); the test module clones one
  template.
