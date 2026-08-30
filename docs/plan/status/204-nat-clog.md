# Lane: nat-clog — `Nat.clog` exists, transferred verbatim from `Nat.log`

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, nat-clog, 2026-08-28).**

Four boundary facts (`clog_zero_left`, `clog_zero_right`, `clog_one_left`,
`clog_one_right`) were `BLOCKED` on an undeclared kernel definition,
`Nat.clog`. It now exists, with two definitions and four theorems, all
admitted through `Kernel::add_declaration` with an empty `axiom_footprint`.

**The 199-nat-log lane's sketch was RIGHT, and the fuel device transferred
verbatim.** Mathlib v4.30's `Nat.clog b n = if 1 < b ∧ 1 < n then clog b ((n +
b - 1) / b) + 1 else 0` has the same non-structural shape as `Nat.log` — the
recursive call is at `(n + b - 1) / b`, not a constructor predecessor — so it
gets the same treatment: structural recursion on a FUEL argument, instantiated
at `n` itself.

```text
Nat.clogAux b 0        n ≡ 0
Nat.clogAux b (succ f) n ≡ if 2 ≤ b then (if 2 ≤ n then succ (clogAux b f ((n + b - 1) / b)) else 0) else 0
Nat.clog b n           := Nat.clogAux b n n
```

Both equations are definitional (β/δ/ι); nothing here appeals to an axiom.

**One design point differs from `log.rs`, and it is the guard nesting order —
the OPPOSITE of `log`'s.** `log`'s guard mixed a `b`-only cut (`2 ≤ b`) with a
cut relating `b` and `n` (`b ≤ n`), and needed the mixed cut outermost for
`log_of_lt`. `clog`'s guard (`2 ≤ b ∧ 2 ≤ n`) has **two single-variable cuts**,
and the four theorems this lane proves split cleanly: `clog_zero_left`/
`clog_one_left` fix `b` and vary `n`, so they need the `b`-only cut (`2 ≤ b`)
outermost to collapse in one rewrite regardless of `n`; `clog_zero_right`
never reaches the guard at all (fuel `0`, pure `refl`); `clog_one_right` fixes
`n = 1`, so its `n`-only cut (`2 ≤ 1`) is a closed `false` no matter which
branch of a 3-way case split on `b` it is reached from. `2 ≤ b` outermost
serves every theorem here, so — unlike `log`, where the ordering was a real
tradeoff against `log_of_lt` — there was no tension to resolve.

Detail moved to [`../notes/204-nat-clog.md`](../notes/204-nat-clog.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-clog | `Nat.clog` by structural fuel recursion, transferred verbatim from `Nat.log` — 2 definitions, 4 theorems, all axiom-free; 4 facts closed (`clog_zero_left`, `clog_zero_right`, `clog_one_left`, `clog_one_right`); `clog_pos`/`log_le_clog` sized as a separate generalized-induction task |
