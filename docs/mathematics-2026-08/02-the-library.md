# 02 — The library: ℕ → ℤ → ℚ → ℝ

> **This rung is owned by another lane.** `crates/axeyum-lean-kernel/` is being
> worked continuously by a second session — 69 commits in 24 hours, 49 of them
> touching `nat_prelude.rs`. Everything below is therefore a *description of
> where the library stands and what it unlocks*, not a work queue for this
> strand. The two hazards in the last section are real and are **not ours to
> fix**. See
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).
>
> What *is* ours is the receiver: an UNSAT evidence route for `Int`/`Real`
> (engineering `01` K2), so that results about ℤ can carry a negative control
> the moment ℤ exists. Today `axeyum-scenarios` `unreachable!()`s on both sorts.

> **STATUS 2026-08-16 — ℤ is done (0 axioms), and ℚ is scoped. The construction
> named below is not the one to build.**
>
> This document says ℚ is "a quotient of ℤ×ℤ≠0 by cross-multiplication". That is
> the mathematics; it is not how a kernel does it, and here it is *inexpressible*
> — this kernel's quotient package has no `Quot.sound`.
>
> **Prior art, read rather than guessed.** Lean 4.30.0's own source is installed
> on this fleet, and Lean core does not use a quotient either
> (`Init/Data/Rat/Basic.lean`):
>
> ```lean
> structure Rat where
>   num : Int
>   den : Nat := 1
>   den_nz : den ≠ 0
>   reduced : num.natAbs.Coprime den
> ```
>
> A structure carrying a *normalised representative* plus two proof fields, with
> `Rat.normalize` reducing by the gcd. That is the same move this project already
> made for ℤ — normalised pairs over a setoid quotient, chosen because
> `Quot.sound` is admitted as a trusted `Declaration::Quotient` and would land in
> every downstream footprint. The decision generalises, and the most-used
> implementation of ℚ in the world agrees with it.
>
> **Kernel support confirmed**, not assumed: `Exists.intro` is already a
> constructor taking a witness *and* a proof, so multi-field constructors with
> `Prop` fields work, and structure eta is implemented in `tc.rs`.
>
> **Measured gap list** (from `IntPrelude`/`NatPrelude` declaration inventories,
> not from a doc). Present: the whole ℕ division/gcd development — `div`, `mod`,
> `gcd`, `dvd`, `div_mod_exists`/`_unique`/`_bounds`, `div_mod_exact_exists`,
> `gcd_bezout`, `dvd_gcd_iff` — and ℤ with its ring and order laws, axiom-free.
> Absent, and needed:
>
> | missing | note |
> |---|---|
> | `Int.natAbs` | trivial by `Int.rec`; `ofNat n ↦ n`, `negSucc n ↦ succ n` |
> | `Int.div` / `Int.mod` | **genuinely new work.** The axiom did *not* need them — it is existential — so this was correctly skipped then and cannot be skipped now |
> | `Int.sub` | not declared; `add a (neg b)` may serve without a new definition |
> | `Nat.Coprime` | no named notion, but `gcd a b = 1` is immediate from what is proved |
>
> **The payoff worth naming:** `Int.euclidean_decomposition`, just proved, is
> exactly the *specification* `Int.div`/`Int.mod` have to meet. Defining them by
> sign cases over `Nat.div`/`Nat.mod` and proving they satisfy it turns a freshly
> derived theorem into the contract for the next layer — which is the flywheel
> doing what it is for.
>
> Suggested order: `natAbs` → `Int.div`/`Int.mod` against the decomposition →
> `Coprime` → the `Rat` structure → `normalize`.

**The state.** One number system is proved. The rest are assumed or absent.

```
nat_prelude     106 proved theorems      0 axioms
int_prelude       0 proved               3 axioms
arith_prelude     0 proved               3 axioms
string_prelude    0 proved               1 axiom
```

`nat_prelude.rs` went **3,856 → 9,969 lines in 60 commits during a single
session**, and — this is the part that matters — it left arithmetic behind:

```
add native accessibility foundation   ·  add generic well-founded fixpoint
prove well-founded fixpoint equation  ·  prove Nat strict order well-founded
add executable Nat division state     ·  certify executable Nat division
add checked executable Nat gcd        ·  prove Nat gcd universal property
bridge divisibility through executable remainder
```

Well-founded recursion, certified division, gcd with its universal property.
That is the machinery every later construction needs, and it landed in hours.

## Why the library is the rung everything waits on

A proof assistant with no library can state almost nothing. `Int` being
axiomatized is not a cosmetic gap: **every theorem above it inherits three
assumptions**, and the reconstruction routes that lift solver results into the
kernel land in a world where ℤ is postulated rather than constructed.

It also bounds the mathematics strand's other rungs:

- [`01`](01-decide-vs-certify.md): a certificate is a term in a language. If the
  language has no ℚ, there is no ℚ certificate.
- [`03`](03-symbolic-and-infinite.md): a theorem about an infinite family of
  integers needs ℤ to be a *thing*, not an axiom set.
- The engineering strand's `01` is the same item viewed as plumbing; this is the
  same item viewed as content.

## The construction order

Standard, and each step is a genuine mathematical obligation, not a port:

| step | construction | what it needs from below |
|---|---|---|
| **ℤ** | quotient of ℕ×ℕ by `(a,b) ~ (c,d) ⟺ a+d = c+b` | ℕ addition, its cancellation law, and a quotient former |
| **ℚ** | quotient of ℤ×ℤ≠0 by cross-multiplication | ℤ ring structure; ℕ gcd for normal forms |
| **ℝ** | Cauchy sequences or Dedekind cuts over ℚ | ℚ ordered-field structure; completeness is the real work |

**ℤ is reachable now.** `add_left_cancel` and `add_right_cancel` are proved;
well-founded recursion is proved; the kernel has quotient support
(`quotient.rs`, with a canonical-package gate on the import side). The
obligation is real work but it is *bounded* work, and the payoff is countable:
three assumptions discharged, and every downstream statement about integers
stops resting on them.

**ℚ is the interesting one for us**, because `gcd` and its universal property
just landed — normal forms for rationals are exactly what that unlocks.

**ℝ is a different order of effort** and should be scoped, not attempted. Note
what depends on it: the curriculum marks `reals` as `status = "covered"`, and
the corpus audit found it is the one `covered` node our fragment cannot support.

## The metric

**Assumptions remaining, per prelude, per release.** Today: `int` 3, `arith` 3,
`string` 1, `nat` 0.

It is a good metric for three reasons. A referee can check it in one command. A
competitor cannot fake it. And it moves monotonically in the direction the
project claims to care about — a smaller trusted base — rather than measuring
speed, which the project explicitly does not lead with.

Publish it beside the capability count, not buried in a plan.

## Two hazards already visible in the library

Both found by a peer session and both blocked on file ownership at the time:

1. **`nat_prelude.rs:8090`** — `.expect("sum permutation target must contain the
   same atoms")` panics if the target is not a permutation of the source.
   Private, two callers, safe today. The module grew 2.6× in one session and the
   caller count grows with it.
2. **`prove_left_sum_permutation` is bubble sort with a full rebuild in the
   inner loop** — O(n²) adjacent swaps, each calling an O(n) fold, so O(n³)
   interner lookups and an O(n²)-node proof term with a left-nested `trans`
   spine. In the finder's words: *"invisible at Rado's n; a cliff for anything
   larger."* The fix is small — rebuild from the swap index forward, since
   everything below it is unchanged.

The second is this strand's problem in miniature: **an algorithm chosen for the
scale we happened to test, inside the artifact meant to scale.** A library is
not a benchmark; it will be called at sizes nobody anticipated, and its proof
terms are consumed by a kernel whose cost is linear in their size.

## What to do first

1. **ℤ from proved ℕ.** Discharge the three `int_prelude` assumptions. Bounded,
   countable, and it is the keystone both strands identified independently.
2. **Then `arith_prelude`'s three**, which likely fall out of ℤ.
3. **Fix the two hazards above** before the module doubles again.
4. **Scope ℚ** once ℤ lands — `gcd` and its universal property make normal forms
   tractable, and ℚ is the last rung before the effort profile changes shape.
5. **Do not start ℝ** without an explicit decision. Scope it, cost it, and
   decide deliberately — and until then, correct the curriculum's `reals` node
   rather than leaving it marked `covered`.
