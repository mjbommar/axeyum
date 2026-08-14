# Diary: constructing ℤ over the proved ℕ development

Lane: `int-keystone`. Date: 2026-08-14.

## The hole

Measured before starting:

```
$ cargo run --release -q -p axeyum-lean-kernel --example nat_axiom_inventory 2>&1 >/dev/null
logic:   axiom=0  opaque=0 quotient=0 total_trusted=0
nat:     axiom=0  opaque=0 quotient=0 total_trusted=0
real:    axiom=30 opaque=0 quotient=0 total_trusted=30
integer: axiom=34 opaque=0 quotient=0 total_trusted=34
string:  axiom=1  opaque=0 quotient=0 total_trusted=1
```

`nat` is the project's headline metric: 119 theorems, zero trusted declarations.
`integer` was the opposite — 34 axioms and, per `theorem_axiom_footprint`, **two**
`Declaration::Theorem`s, both of which were `Acc.inv` and `WellFounded.fix_eq`,
generic well-founded-recursion scaffolding that the logic prelude contributes and
that says nothing about ℤ. ℤ was asserted, not derived. An earlier extraction lane
had declined to record *any* integer fact rather than write a footprint it could
not justify, which was the correct call and also the reason this lane exists.

## Result

```
integer: axiom=8  opaque=0 quotient=0 total_trusted=8
```

34 → 8. The 26 that went away split into two kinds, and the distinction matters
when reading the number:

- **8 were the carrier and the operations** (`Int`, `add`, `mul`, `neg`, `zero`,
  `one`, `le`, `lt`). These became an inductive type and checked definitions.
  Removing them is not "proving" anything; it is *constructing* the object the
  laws are about, which is the prerequisite for proving any of them.
- **18 were laws**, and each is now a `Declaration::Theorem` whose
  `Kernel::axiom_footprint` is **empty**:

  `le_refl`, `le_trans`, `lt_irrefl`, `lt_trans`, `lt_of_lt_of_le`,
  `lt_of_le_of_lt`, `le_of_lt`, `le_total`, `lt_of_le_of_ne`, `zero_lt_one`,
  `no_int_between`, `add_zero`, `add_comm`, `add_neg`, `mul_zero`, `mul_one`,
  `mul_comm`, `mul_nonneg`.

Still asserted (8): `add_assoc`, `mul_assoc`, `left_distrib`, `add_le_add`,
`add_lt_add_of_le_of_lt`, `mul_le_mul_of_nonneg_left`, `eq_em`,
`euclidean_decomposition`.

The headline theorem is `Int.no_int_between` — discreteness, the fact the ordered
field ℝ does not have and the one an integer-cut refutation actually invokes. It
was the integer route's central *assumption*; its footprint is now `[]`.

## The representation decision, and why the textbook route loses here

The obvious construction is the setoid quotient of `ℕ × ℕ` by
`(a,b) ~ (c,d) ⟺ a+d = c+b`. **In this kernel that route is strictly worse, and
the reason is measurable rather than aesthetic.**

`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and `Quot.sound` are admitted as
`Declaration::Quotient` — a *trusted* kind, which `nat_axiom_inventory` counts in
its own column precisely because `Quot.sound` is one of the three declarations
Lean's own `#print axioms` reports. Every integer theorem proved over a quotient
would name `Quot.sound` in its footprint forever. The number would have gone from
`axiom=34 quotient=0` to something like `axiom=0 quotient=5`, and no integer fact
could have carried `axiom_footprint: []`. That is not a smaller assumption; it is
the same assumption relabelled.

So I took Lean's own route: `Int` is an inductive with `Int.ofNat n` (for `n ≥ 0`)
and `Int.negSucc n` (for `-(n+1)`). Each integer has exactly one representative,
so `Eq Int` is ordinary propositional equality and no quotient is needed.

Worth recording precisely *where* the naive alternative fails, because most of the
ring laws do **not** distinguish the two. On the raw pair `(a,b)` meaning `a-b`,
with `(a,b)+(c,d) = (a+c, b+d)`, addition is commutative and associative and
multiplication is commutative — all by componentwise `Nat` lemmas, up to
structural equality. The law that breaks is exactly `add_neg`:
`(a,b) + (b,a) = (a+b, b+a)`, which is not the pair `(0,0)`. **One law forces the
quotient**, and avoiding it is what the normalized constructors buy.

## What made the proofs cheap, and what did not

`Int.le` and `Int.lt` are defined by cases into `Nat.le`/`Nat.lt` rather than as
`NonNeg (b - a)`:

| | `ofNat n` | `negSucc n` |
|---|---|---|
| `ofNat m` | `Nat.le m n` | `False` |
| `negSucc m` | `True` | `Nat.le n m` |

That decision is why ten order laws fell out almost immediately. In every mixed
branch, either a hypothesis has *already* ι-reduced to `False` (so `False.rec`
closes it) or the goal has reduced to `True`. Only the two same-sign branches do
work, and they are the corresponding `Nat` lemma — with the arguments swapped in
the `negSucc`/`negSucc` branch, since `-(m+1) ≤ -(n+1)` is `n ≤ m`.

`zero_lt_one` reduces to `Nat.le 1 1`, i.e. `Nat.le.refl`. `le_trans` is eight
branches of which six are trivial. `no_int_between` is two branches, one of which
is the hypothesis itself.

Three more laws are pure `Eq.refl` once the definitions are written the right way:

- `add_zero` — `Nat.add x zero ≡ x` handles `ofNat`, and `Nat.sub x zero ≡ x`
  makes `subNatNat 0 (succ m)` ι-reduce straight back to `negSucc m`.
- `mul_zero` — `Nat.mul x zero ≡ zero` and `negOfNat 0 ≡ ofNat 0`.
- the two mixed branches of `add_comm` — I defined
  `ofNat m + negSucc n := subNatNat m (succ n)` and
  `negSucc n + ofNat m := subNatNat m (succ n)`, so those branches are *literally
  the same term*. Choosing the argument order deliberately turned a proof
  obligation into `Eq.refl`.

`add_neg` was the only derived law needing a real lemma. `Int.subNatNat m n` puts
`Nat.sub m n` in its non-negative value **and** `Nat.sub n m` in its scrutinee; on
the diagonal both are `Nat.sub n n`, so the diagonal is a one-hole context and a
single rewrite by `Nat.sub_self` collapses the whole thing to `Int.ofNat 0`. It
also needed a second split — `Int.neg (ofNat n)` is `Int.negOfNat n`, which is
*stuck* on a variable `n`, so the non-negative branch has to case on `n` as well.

## Why the remaining eight are the remaining eight

They are not a random tail. Seven of the eight require reasoning about
`Int.subNatNat`'s **borrow** — which constructor the answer lands in — across a
case split the definitions do not resolve:

- `add_assoc`, `left_distrib`, `add_le_add`, `add_lt_add_of_le_of_lt`,
  `mul_le_mul_of_nonneg_left` all mix `Int.add` (whose mixed branches are
  `subNatNat`, stuck on variables) with a second operation or relation. Eight to
  sixteen branches each, and the interesting ones need lemmas like
  `subNatNat m n = subNatNat (m+k) (n+k)` and a characterization of when
  `subNatNat` returns `ofNat`. That is a real sub-development, not a longer proof
  of the same shape as the ones above, and I stopped rather than half-build it.
- `mul_assoc` needs `negOfNat (m * n)` to commute with the sign bookkeeping in
  all eight branches.
- `eq_em` needs two things this development does not have: constructor
  discrimination (`ofNat m ≠ negSucc n`, via a `Prop`-valued discriminator built
  with `Int.rec`) and decidable `Nat` equality lifted from `Nat.beq`. Both are
  reachable — `Nat.beq_eq_true_iff` and `NatOps::false_true_elim` exist — and this
  is the cheapest of the eight to attack next.
- `euclidean_decomposition` needs integer division and is the hardest.

## Two consequences I did not hide

**`build_int_prelude` now builds the `Nat` prelude first.** Measured: `Nat`
prelude 52 ms, old `Int` prelude 3 ms. `IntReconstructCtx::new` builds a fresh
kernel per reconstruction context, so integer proof emission costs ~52 ms more
per context. That is the price of the construction and it is not obviously
optimal — a lane that cares could split the `Nat` prelude so `Int` pulls only the
arithmetic and order fragments and not the gcd/Bézout development.

**A failed `Int` build no longer rolls the `Nat` prelude back.** The prerequisites
are admitted before the `Int` checkpoint, so `prelude_composition`'s
"a failed package build must be atomic" test had to be told to build `Nat` first.
This is not new behaviour in kind — `build_logic_prelude` was always called before
the checkpoint and always survived a failed `Int` build — but it is new in scale,
and the docstring's "leaves the pre-call environment unchanged" now means "leaves
the prerequisites, and unwinds every `Int` declaration".

## What I would tell the next person

**Type-checking the laws does not pin the operations down.** This is the trap that
matters here and it is subtle: a *wrong* `Int.add` would satisfy a
wrong-but-provable `Int.add_comm`, and every gate in this repository would stay
green. The construction is only meaningful if the operations compute the right
answers, so `the_operations_compute_their_normal_forms` evaluates 16 binary
operations and 5 negations by kernel reduction against their normal forms,
covering every sign combination *including* the borrow cases (`3 + (-3) = 0` and
`1 + (-3) = -2` are both in the table). Do not add an operation here without
adding its rows.

**Share the statement builder between the two routes.** `statements.rs` holds each
law's statement exactly once; the axiom route wraps it in an `Int` telescope and
declares an `Axiom`, the theorem route wraps the same thing and declares a
`Theorem`. That is why the types are byte-identical across the change and why no
downstream proof term needed touching. If the statement were written twice, a law
could silently *weaken* on its way from assumption to consequence and the axiom
count would still look like progress.

**Assert the footprint, not just the count.** Eight integer laws are still
asserted. A "derived" law that quietly applied one of them would type-check and
would shrink no count. `derived_laws_have_no_axiom_footprint` asserts `[]` per
theorem; that is the check that makes the number mean what it says.

**`Or.rec` takes no universe parameter; `And.rec` takes one.** Cost me one failed
build. `Or` is a `Prop` with two non-subsingleton constructors, so it eliminates
only into `Prop` and the recursor carries no motive level. `Kernel::const_` was
called with `vec![zero]` and the error surfaced as
`UniverseArityMismatch { name: NameId(19), expected: 0, got: 1 }` — a `NameId`,
which says nothing on its own. Resolving it meant dumping the environment.

**The suites you want are `#![cfg(feature = "full")]`.** Running
`cargo test -p axeyum-solver --test diophantine_lean_reconstruct` without
`--features full` printed `running 0 tests ... ok` and exited 0, exactly as
`CLAUDE.md` warns. With the feature it ran 5 and caught the golden-hash change.

## Independent checking: what was and was not done

- The kernel type-checked every proof term at admission — that is what
  `Declaration::Theorem` through `Kernel::add_declaration` means, and it is a
  genuine machine check.
- `cargo test -p axeyum-lean-kernel`: green, 249 lib tests plus every integration
  suite. `cargo test -p axeyum-solver --lib --features full`: 1140 passed.
- The Diophantine and integer-inequality Lean reconstruction suites pass with
  `--features full`.
- **Not done: no independent Lean binary checked the exported module.** No `lean`
  is installed on this machine and `AXEYUM_LEAN_BIN` is unset, so
  `diophantine_module_checks_in_real_lean` and its siblings took the skip path and
  still reported `ok`. The exported module grew from 1,004,665 to 1,041,898 bytes
  because `Int` is now an inductive with a recursor rather than an axiom, and
  **nothing outside this repository has read those bytes.** The module opens with
  `prelude` (no `import Init`), so the re-declared `Int` should not collide with
  Lean's own — but "should" is the operative word. Anyone with Lean available
  should run that suite with `AXEYUM_REQUIRE_LEAN=1` before treating the export as
  validated.
