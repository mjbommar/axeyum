# Lane: int-two-sided-induction — two-sided induction over ℤ, and `Int.fib_add`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, int-two-sided-induction, 2026-08-29).** The stated
deficiency — "no two-sided (`ofNat`/`negSucc`-covering) induction combinator
exists anywhere in `int_prelude/`" — is closed, and so is the keystone it
blocked. Three declarations landed, all axiom-free, **all three accepted by the
kernel on the first attempt; nothing was rejected in this lane.**

- `Int.induction_on` (`int_prelude/two_sided_induction.rs`) —
  `∀ P, P 0 → (∀ n, P n → P (n+1)) → (∀ n, P n → P (n-1)) → ∀ n, P n`.
- `Int.fib_rec` (`int_prelude/fibonacci.rs`) — `fib (n+2) = fib (n+1) + fib n`
  at **every** integer index.
- `Int.fib_add` (`int_prelude/fibonacci.rs`) — Mathlib's statement verbatim,
  `fib (m+n) = fib (m-1) * fib n + fib m * fib (n+1)`.

`int_prelude::` went **40 → 44 passing**, `derived_laws` 151 → 154, integer
trusted surface still 0.

**The question the brief asked: `Int.fib_add` did NOT reduce to `Nat.fib_add`
plus sign bookkeeping.** `Nat.fib_add` (`fib (succ (m+n)) = fib m * fib n +
fib (succ m) * fib (succ n)`) is exactly this statement restricted to
`m ≥ 1, n ≥ 0` — one of four constructor pairs, and not even all of the
non-negative case: at `m = 0` the leading coefficient is `fib(-1)`, a value at a
negative index. The proof uses `Nat.fib_add` nowhere.

**But the combinator was CHEAP, against the prior sizing of "genuinely
comparable-or-more effort than the theorem it blocks".** ℤ's operations are
nested `Int.rec` over ℕ, so at a *constructor* argument every bridging step
computes, and no equation lemma is needed anywhere:

| step | reduces to | why |
| --- | --- | --- |
| `add (ofNat k) one` | `ofNat (succ k)` | `Nat.add` recurses right and the right argument is the literal `1` |
| `sub zero one` | `negSucc 0` | `Int.sub` is a plain `Definition`; `subNatNat` scrutinises the closed `Nat.sub 1 0` |
| `sub (negSucc k) one` | `negSucc (succ k)` | again the literal is on the right |

Detail moved to [`../notes/238-int-two-sided-induction.md`](../notes/238-int-two-sided-induction.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-two-sided-induction | `Int.induction_on`: two-sided induction over ℤ, the first combinator in `int_prelude/` that inducts rather than case-splits |
| 2026-08-29 | int-two-sided-induction | `Int.fib_rec`: the Fibonacci recurrence at every integer index, negative ones included |
| 2026-08-29 | int-two-sided-induction | `Int.fib_add` closed (`F:ml430-int-fib-add-181b6a2c` open → proved); it does NOT reduce to `Nat.fib_add` |
