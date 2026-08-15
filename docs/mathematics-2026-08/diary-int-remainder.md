# Diary: the `subNatNat` borrow, and five of the last six integer axioms

Lane: `int-remainder`. Date: 2026-08-15. Predecessor:
[`diary-int-keystone.md`](diary-int-keystone.md).

## Measured before and after

```
$ cargo run --release -q -p axeyum-lean-kernel --example nat_axiom_inventory 2>&1 >/dev/null
                                       before                 after
logic:   axiom=0  opaque=0 quotient=0   unchanged
nat:     axiom=0  opaque=0 quotient=0   unchanged
real:    axiom=30 opaque=0 quotient=0   unchanged
integer: axiom=6  opaque=0 quotient=0   axiom=1  opaque=0 quotient=0
string:  axiom=1  opaque=0 quotient=0   unchanged
```

Discharged: `Int.add_assoc`, `Int.mul_assoc`, `Int.left_distrib`,
`Int.add_le_add`, `Int.add_lt_add_of_le_of_lt`.
Remaining: `Int.euclidean_decomposition`.

```
$ cargo run --release -q -p axeyum-lean-kernel --example int_theorem_inventory | tail -1
Int: 50 derived (50 with an EMPTY axiom footprint), 1 still asserted
```

20 → 50 theorems. `theorem_axiom_footprint` prints `0` in the footprint column
for all 50; the one axiom prints its own name, which is the negative control that
makes the zero mean something.

## What the wall actually was

`Int.subNatNat m n` is

```
Nat.rec (fun _ => Int) (Int.ofNat (m - n)) (fun k _ => Int.negSucc k) (Nat.sub n m)
```

Both `Nat.sub`s are stuck on variables, so the whole term is stuck, and *every
mixed-sign branch of `Int.add` is one of these*. That is the entire reason four
laws were undischarged: each mixes `Int.add` with a second operation or relation,
and the branch where the signs disagree cannot reduce far enough for any `Nat`
lemma to apply. It is one obstruction wearing four hats, exactly as the previous
lane recorded.

The two `Nat.sub`s sit in **different holes** — one is the `Nat.rec`'s zero minor,
the other its major premise — so no single one-hole context covers both and every
rewrite of `subNatNat` is two rewrites. That is the first thing to know before
writing any of these proofs.

## The three steps

**1 — Shift.** `subNatNat (m+k) (n+k) = subNatNat m n`. This is the only
non-trivial equation a stuck `subNatNat` satisfies, and everything else is a
corollary. Induction on `k`: `Nat.add` recurses on its second argument, so
`m+(k+1)` is *definitionally* `(m+k)+1` and the step is the one-shot
`subNatNat (m+1) (n+1) = subNatNat m n` — `Nat.succ_sub_succ` applied to the
value, then to the scrutinee, composed by transitivity. The base case is
`Eq.refl` because `m+0 ≡ m`.

**2 — Two anchors, then two characterisations.**
`subNatNat 0 k = negOfNat k` is two `Eq.refl`s: the scrutinee is `k-0 ≡ k`, so
splitting `k` fires the recursor directly. `subNatNat m 0 = ofNat m` is *not*
symmetric to it and is the more interesting of the two: the value `m-0` reduces
on its own, but the scrutinee `0-m` is stuck on `m` even though its answer is
obviously `0`. It needs `Nat.sub_eq_zero_of_le 0 m (Nat.zero_le m)`, i.e. an
order fact, to reduce an arithmetic one.

Shifting each anchor gives

```
subNatNat (n+i) n = ofNat i          subNatNat m (m+k) = negOfNat k
```

and both fall out with *no* rewriting, because `Nat.add x 0 ≡ x` lines the
shifted anchor up with the statement on the nose. Choosing the left-shifted form
of the shift lemma is what buys that; the right-shifted form needs two
`Nat.add_comm` rewrites at every use. Both forms are declared.

**3 — Elimination.** `Nat.le_total m n` plus `Nat.le_dest` says every pair is
`(n+i, n)` or `(m, m+j)`, and the two characterisations cover exactly those. The
packaged principle is

```
Int.subNatNat_elim :
  ∀ (P : Int → Prop) (m n : Nat),
    (∀ i, n + i = m     → P (Int.ofNat i)) →
    (∀ i, m + (i+1) = n → P (Int.negSucc i)) →
    P (Int.subNatNat m n)
```

After it, every blocked lemma is two branches instead of an open-ended stall.

Two details in its proof are easy to get wrong. The `m ≤ n` half must split its
difference again, because a difference of `0` is the **non-borrowing** case and
has to be routed to the first branch, not the second. And the second outcome is
stated as `negSucc i`, not `negOfNat k`: the `negOfNat` form is what the
*characterisation* wants (it keeps `k = 0` in range, which the multiplicative
lemmas need when a scale collapses a factor), but the *elimination* form must be
disjoint from `ofNat`, so a caller learns the sign and not merely the magnitude.
The development uses both, deliberately.

## What each law then cost

- **`add_assoc`** — four re-association lemmas
  (`ofNat m + subNatNat n q = subNatNat (m+n) q` and its three siblings, two of
  which come free from `Int.add_comm`), then eight branches of `Nat.add_assoc`
  and `Nat.succ_add`.
- **`left_distrib`** — two scaling lemmas
  (`ofNat m * subNatNat p q = subNatNat (m*p) (m*q)`, and the negative one, which
  **swaps the two sides** because a negative scale reverses which end of the
  difference dominates), plus three lemmas for adding stuck `negOfNat`s. Then
  every branch is one `Nat.left_distrib`.
- **`mul_assoc`** — needed none of it, and I should have seen that sooner. It is
  blocked by `negOfNat`, not `subNatNat`: a triple product leaves a stuck
  `negOfNat` under a second multiplication in six of its eight branches. Four
  two-case lemmas unstick it, and then it is `Nat.mul_assoc` wrapped in `ofNat`
  when the number of negative factors is even and `negOfNat` when it is odd. It
  was the first to land and is independent of the whole borrow development.
- **`add_le_add` / `add_lt_add_of_le_of_lt`** — see below.

## The one decision I would call non-obvious

For the two additive order laws the structural route is sixteen branches over an
`Int.add` that is itself stuck in half of them. I did not take it. Instead:

```
Int.le_dest      : le a b → ∃ (i : Nat), b = a + Int.ofNat i
Int.le_ofNat_add : ∀ a i,  le a (a + Int.ofNat i)
```

and the same pair for `lt` with a successor gap. With those, `add_le_add` is one
ring rearrangement — `(a+i) + (c+j) = (a+c) + (i+j)`, five `add_assoc`/`add_comm`
steps — and **`Int.rec` does not appear in the proof term at all**. Sixteen
branches became zero.

That is the transferable part. `Int.le` is *defined* by cases, so it invites case
analysis, and case analysis is what the borrow makes expensive. Replacing the
relation by its witness moves the work to a place where the stuck term never
comes up. The four difference lemmas cost about as much as one of the sixteen
branches would have, and they are reusable: `le_dest` is the natural statement to
hand any later development that needs to compare integers.

The strict version needed one extra observation, and it is a *definitional* one:
`Int.ofNat i + Int.ofNat (j+1)` reduces to `Int.ofNat ((i+j)+1)` without any
lemma, so the strict base case applies with no arithmetic at the join.

## Errors worth recording

**Three of the four bugs I hit were a `symm` in the wrong direction**, and every
one type-checked as a *statement* while being the reverse of what the caller
needed. `two_successors` returned `Eq Nat (((n+q)+1)+1) ((n+1)+(q+1))` when its
own doc comment said the opposite; the kernel's rejection named the two `Nat`
types, which is what let me see it in seconds rather than minutes. The fourth was
`congr(a, b, h, f)` called with `b` one `Nat.succ` short.

None of these is deep. The reason to record them is that the error messages
carried the whole cost: `TypeMismatch { expected: ExprId(81278), got: ExprId(3) }`
is unreadable, and `NatOps::explain` — which renders both sides — turned each of
them into a ten-second fix. I wrapped every declaration in a temporary
`explain`-printing shim while developing and removed it before committing. If you
are writing proof terms in this DSL, do that first; do not try to read `ExprId`s.

**The first real bug was a carrier confusion, not a logic error.** I reached for
`IntDev::icongr` (congruence at `Int`) to lift a `Nat` equation, and the kernel
said `expected : Int, got : AxNat`. The right combinator was `nat_eq_to_int`,
which already existed for exactly this. The lesson is narrow but real: this
development has *two* carriers and therefore two of every equality combinator,
and the one you want is usually the cross-carrier one.

## Independent checking: what was and was not done

- The kernel type-checked all 30 new proof terms at admission. That is what
  `Declaration::Theorem` through `Kernel::add_declaration` means.
- **A real Lean binary read the export.** This is the thing the previous lane
  could not do — no `lean` was installed then. `scripts/check-lean-gate.sh` with
  Lean 4.30.0 reports `12 suites, 49 tests, 112 real-Lean checks (floor 105)`,
  green, and the Diophantine module it checks now carries the whole `subNatNat`
  development. The module grew 1,049,867 → 1,142,494 bytes.
- The golden module hash moved. I updated it by having a script parse the
  `left:` tuple out of the failing test's own output and rewrite the constant —
  the previous lane got this wrong by typing a hex constant by hand, and the
  point of automating it is that no digit passes through a human.
- `nat_theorem_inventory` is **byte-identical** before and after: 119 theorems,
  `diff` clean. `nat: axiom=0 opaque=0 quotient=0` unchanged. ℤ grew; ℕ did not
  move.
- `cargo test -p axeyum-lean-kernel`: green, 249 lib tests plus every integration
  suite. `cargo clippy -p axeyum-lean-kernel --all-targets --all-features -D
  warnings`: clean.

## What is left, and why it is a different kind of problem

`Int.euclidean_decomposition` — `0 < k → ∃ q r, t = k·q + r ∧ 0 ≤ r ∧ r < k`.

It is the only remaining integer axiom and the only one that is not a ring or
order law. Every law discharged here is an **equation or an inequality between
terms already in the language**, so the work was always "make the definitions
reduce". This one asserts the *existence* of two integers the language cannot
name, so discharging it means defining integer division and remainder and proving
their specification — a new definition with its own recursion and its own
termination story, not another rewriting lemma.

The `Nat` prelude has the pieces (`Nat.div_mod_exists`, `Nat.div_mod_unique`,
`Nat.mod_lt`, and an executable `Nat.divMod` certified against them), so the
shape is clear: define `Int.div`/`Int.mod` by cases on the dividend's sign over
`Nat.div`/`Nat.mod`, and the negative case is where the interesting work is —
Euclidean rounding is not truncation, and the sign convention has to be chosen
and then defended by the `0 ≤ r < k` bound rather than assumed. `Int.le_dest`
and `Int.subNatNat_elim` are both directly useful there.

I stopped rather than half-build it, for the same reason the previous lane
stopped at the borrow.
