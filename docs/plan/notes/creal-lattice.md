# Notes: creal-lattice

Detail kept out of [`../status/69-creal-lattice.md`](../status/69-creal-lattice.md)
so the lane block stays inside the per-lane ceiling (ADR-0507). The decision is
[ADR-0519](../../research/09-decisions/adr-0519-the-real-lattice-is-defined-on-the-representation-and-is-one-lipschitz.md);
its predecessors, which costed this slice without building it, are
[`creal-field.md`](creal-field.md) and [`creal-inv.md`](creal-inv.md).

## Why this slice, ahead of cotransitivity and `apart_mul`

Three were costed and unbuilt: `abs`/`max`/`min` (~500), cotransitivity of `lt`
(~400), `apart_mul` (~300). Cotransitivity is the more *important* one — it is
the workhorse the rest of constructive analysis rests on — and it was still the
wrong one to take first, for a reason specific to this development rather than
to the mathematics:

**cotransitivity needs an index computation and the lattice does not.** The
inverse lane measured that a *wrong* sampling index takes **1,043 s to be
refused** against 78 s to be accepted, so an index slice's failure mode is a run
that looks like a hang, and a bisect across one is hours. The lattice has no
index at all — `max` is pointwise — so every refusal in it comes back at the
speed of an ordinary type error. On a contended box that is the difference
between a slice that lands and one that does not.

It also does not make cotransitivity more expensive: its cost is dominated by
the two estimates and the index, neither of which the lattice touches. And it
supplies the *shape* every later metric statement is written in (`|x − y| ≤ ε`),
so completeness and Cauchy-ness can now at least be stated the way the
literature states them.

## The obstacle the brief said to verify, verified

The brief said the expected obstacle — a case split on a `Prop` — is
"avoidable: `Rat.abs` is a definition on the representation, not a case split",
and asked that this be checked before being relied on. It is true, and the
reason is worth stating precisely, because the obvious reading is wrong in the
same way ADR-0510's was.

`Rat.le_or_lt` is **proved**. It is also `Or`-valued, hence a `Prop`, and
`Or.rec` does not eliminate into `Type`. So `max` cannot be *derived* from the
decidability of `ℚ`'s order even though `ℚ`'s order is decidable. What works is
not "`abs` is a definition" in general — it is that **`Rat.le a b` is
definitionally `Int.le (num a · den b) (num b · den a)`**, so the sign of the
cross-difference is an `Int`, an `Int`'s sign is a **constructor**, and
`Int.rec` eliminates at every universe. The decision is taken on the
representation, once, and never on `CReal`.

Two consequences the costing did not anticipate:

- **`Rat.abs` is still not needed.** `CReal.abs x := max x (neg x)`, so the ℚ
  fact it wants is `zero_le_max_neg : 0 ≤ max a (−a)`, three lines from
  `le_total`. The four-way sign split over `|a| − |b| ≤ |a − b|` that the ~500
  costing was mostly made of does not appear anywhere.
- **`max` and `min` are the same builder twice.** They differ only in which
  branch returns which argument, so one Rust function emits both definitions,
  one skeleton proves both case principles, and the six laws are three lines
  each. `min` was very nearly free, having been costed as half the slice.

## `max_cases` is the module, and `sub_max_le` is the real construction

```text
Rat.max_cases : ∀ (a b : Rat) (P : Rat → Prop),
  (Rat.le a b → P b) → (Rat.le b a → P a) → P (Rat.max a b)
```

Six of the nine ℚ lattice theorems are one application of this with `P`
instantiated, and both branches discharged by a hypothesis or by `le_refl`.
There is exactly **one** `Int.rec` in the module — the same factoring discipline
`inv_body` established, with `lattice_body` shared between the definition and
the split so a changed definition fails at the kernel rather than leaving the
proof about a stale copy.

The ℝ side rests on one lemma:

```text
Rat.sub_max_le : a − c ≤ q → b − e ≤ q → max a b − max c e ≤ q
```

`max` is one-Lipschitz **jointly**, so it does not degrade the modulus and
`CReal.max` samples at the same index as its arguments — the first operation
since `CReal.neg` for which that is true (`add` at `2n+1`, `mul` at a computed
shift, `inv` at `(C+1)n + C`). And the same lemma, fed the two `Equiv`
hypotheses instead of the two regularity facts, **is** the congruence: one Rust
helper (`creal::lattice::lattice_within`) is regularity *and* congruence for
both operations. That is where the volume saving actually came from.

`sub_min_le` is **not** the dual by rearrangement. `min a b ≤ min (c+q) (e+q)`
still owes `min (c+q) (e+q) ≤ min c e + q`, which is another case split;
splitting on `min c e` directly pays nothing, because in each branch the bound
*is* one of the two hypotheses.

## Vacuity was not the risk here. Degeneracy was

Every statement about `CReal.inv` is guarded by `PosBound x k`, and the inverse
lane's control exists because an uninhabited guard would make all of them hold
footprint-free. **Nothing in this module has a side condition**, so that trap
does not apply — and the *other* trap does, harder:

- `max x y := x` satisfies `le_max_left` by reflexivity;
- `abs x := x` satisfies `le_abs_self`, `neg_le_abs` **and** `abs_le` —
  footprint-free, statements verbatim.

So two theorems are proved from the laws alone and consumed rather than named:
`CReal.not_le_zero_neg_one` (mentions no lattice operation; it exists to be
contradicted) and `CReal.not_equiv_abs_neg_one` — **`abs` is not the identity**.
The witness example's exit status depends on both. The tests additionally admit
`Equiv (max x x) x`, `¬ Equiv (max 0 1) 0` and `¬ Equiv (min 0 1) 1` through the
kernel, and one level down check that `Rat.max`/`Rat.min` **compute** on both
branches — including a negative argument, the `negSucc` branch no law exercises
— with the wrong answer REFUSED.

## Guards, measured rather than asserted

Measured in a `scripts/lane-snapshot.sh` tree at `4c7af898d`.

Baselines: `--lib creal::creal_tests::the_lattice` **3 passed** (128.8 s);
`--lib creal::creal_tests::every_creal_declaration` **1 passed** (62.2 s);
`--lib creal::` **27 passed, 0 failed** (2,229 s under contention, 24 before
this lane).

- **Deleting `CReal.not_equiv_abs_neg_one`** (the `add_declaration` replaced by
  a no-op, so the mutant still builds): **3 tests die**, 1 survives. Dead: the
  declaration inventory, the verbatim-statement test, and the non-degeneracy
  test — which fails with the kernel's own `UnknownConst`, i.e. it was
  *consuming* the guard rather than naming it. The survivor is the negative-
  control test, and that is inherent: it asserts `is_err()`, so "refused because
  false" and "refused because the constant does not exist" are indistinguishable
  to it — exactly the limitation `creal-inv.md` recorded, reproduced here rather
  than assumed.
- **Not measured: perturbing `Rat.max`'s branch selection.** Predicted to remove
  a *mechanism* rather than a guard (`max_cases`'s type would name `Rat.max` and
  its proof would select the other branch, so the ℚ prelude fails to build and
  every test dies). It is cheap to run — `--lib rat_prelude::` is ~6 s, not the
  minutes the ℝ side costs — and is the first thing to do if this module is
  touched.

## What is deliberately not here, with costs

- **No cotransitivity of `lt`** (`x < y → ∀ z, x < z ∨ z < y`). Still ~400
  lines, still the most valuable next rung, and now the *only* one of the three
  costed slices left below `sqrt`. From the gap `q`, compute `r` with `8r < q`,
  compare `z_N` against `x_N + 4r` on `Rat.le_or_lt`, both branches close. Two
  estimates of `le_add_of_nonneg`'s size plus the index computation — and it is
  the index computation that makes it a slice of its own, for the 1,043 s reason
  above.
- **No `apart_mul`** (~300). `CReal.mul_pos` is one of its four sign cases; the
  other three need `lt x zero ↔ lt zero (neg x)` and `(−x)·(−y) ≈ x·y` over
  `Equiv`. Neither exists, and neither is hard.
- **No `Equiv (abs x) x ∨ Equiv (abs x) (neg x)`.** A decision on the sign of a
  real. Not available, not an omission.
- **No `max_comm`, `max_assoc`, `max a a = a` as a `ℚ` identity, no
  `max (a+q) (b+q) = max a b + q`.** Each is one more `max_cases`; nothing
  consumes them. The `ℝ`-level `Equiv (max x x) x` exists only as a test.
- **No `CReal.neg_le_neg`, no `CReal.neg_neg`.** `min` was built pointwise
  through `Rat.min` rather than as `neg (max (neg x) (neg y))` precisely to
  avoid needing them; they remain unbuilt and are the cheapest missing piece of
  the ordered-group toolkit one level up.
- **No `sqrt`, no completeness, no suprema.** Each its own ADR. `abs` gives them
  their *statement* shape and nothing more.
- **No Markov's principle in any disguise.** `¬(x ≈ 0) → x # 0` is not proved,
  not assumed, not used.

## Numbers

- `CReal` declarations **76 → 94**; `Rat` gains **15**. Every one accepted on
  first submission.
- `-p axeyum-lean-kernel --lib`: **375 → 382** tests (3 `CReal`, 4 `Rat`).
  Filtered `creal::` 27 passed / 0 failed; filtered
  `rat_prelude::rat_prelude_tests::the_rational_lattice` 3 passed / 0 failed.
- `creal_setoid_witness`: `94 declarations admitted, trusted surface = 0
  (empty) … abs is not the identity = true`, exit 0.
- `nat_axiom_inventory --include-constructed`: `creal` and `rat` both
  `axiom=0 opaque=0 quotient=0 total_trusted=0`, **unchanged** — and the flag is
  what makes `creal` appear at all.
- `gen-lean-axiom-ledger.py --check`: `total=30 … creal=0 rat=0 real=30`,
  unchanged. No lattice law is one of the 22.
- `validate-facts.py`: 126 facts, 0 errors.
- **Stable** clippy (`-p axeyum-lean-kernel --all-targets --all-features -D
  warnings`) and `RUSTDOCFLAGS="-D warnings" cargo doc`: both clean.
- Source: `rat_prelude/lattice.rs` 893 lines, `creal/lattice.rs` 797, of which
  ~180 are module documentation. Against a ~500-line costing — the volume was
  under-estimated, the difficulty over-estimated.
- A fresh `build_creal_prelude` goes **61 s → ~60 s** measured warm; the lattice
  adds no measurable build time, which is what "no index shift" buys.
