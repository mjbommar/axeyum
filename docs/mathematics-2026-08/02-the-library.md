# 02 — The library: ℕ → ℤ → ℚ → ℝ

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
