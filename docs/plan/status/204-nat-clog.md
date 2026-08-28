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

**`Nat.sub`'s truncation did not bite.** The recursive step builds
`(n + b - 1) / b`, and the subtrahend is the literal `1`; `n + b ≥ 1` for any
reachable `n, b`, so truncation is never exercised on the branch that is
actually selected. It also does not matter for the four boundary lemmas
proved here: each one collapses through the guard before the recursive call
is ever forced, so the subtraction's value on degenerate operands never
enters any proof term.

**What the kernel rejected: nothing.** All six declarations (2 definitions, 4
theorems) were accepted on the first attempt. `every_nat_declaration_is_checked_and_axiom_free`
(reads `kernel.environment()`, not a hand list) initially failed, correctly —
it does not know about a declaration until it is added to `definition_names`/
`theorem_names`, which this lane did.

**Measured `axiom_footprint`:** `[]` for every one of the six declarations —
confirmed both per-theorem (`Kernel::axiom_footprint`) and environment-wide
(`nat_axiom_inventory --require-axiom-free nat` exits 0, `nat: axiom=0
opaque=0 quotient=0 total_trusted=0`).

**`nat_prelude` count:** before this lane, `the_build_is_deterministic` pinned
`69 + 361` (definitions + theorems). After: `71 + 365` (2 new definitions, 4
new theorems), recounted from the test's own render, not hand-incremented.
101 of 929 `nat_prelude::` tests ran (828 filtered by name), all green,
including a new `clog_computes_and_its_boundary_equations_apply` (mirrors
`log_computes_and_its_boundary_equations_apply`, with `clog 2 7 = 3`
deliberately checked against `log 2 7 = 2` so the test cannot pass by
accidentally computing the floor instead of the ceiling).

**Not attempted, deliberately, per the brief's scope:** `clog_pos` and
`log_le_clog` need `clogAux b f n ≤ f` generalized in the motive (`∀ n,
clogAux b f n ≤ f`) — a real induction, not a case split — same tier as
`log`'s `log_le_self`/`log_mono_right`. Also not attempted: flipping the
`F:ml430-nat-clog-*` mirror facts by hand (checker-that-cannot-fail defect;
those are Mathlib's statements, ours is a different definition, and
reconciling them is the autogenesis pipeline's job, not this lane's).

**Gates run:** `cargo check -p axeyum-lean-kernel --lib` clean;
`cargo test -p axeyum-lean-kernel --lib nat_prelude::` 101 passed, 0 failed;
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean;
`cargo fmt --edition 2024 --check` clean on all three touched files;
`python3 scripts/validate-facts.py` 0 errors (1877 facts, up from 1873); all
four new facts' `checker_command`s run directly and confirmed passing
(`nat_theorem_inventory` finds each new name, `nat_axiom_inventory
--require-axiom-free nat` exits 0).

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-clog | `Nat.clog` by structural fuel recursion, transferred verbatim from `Nat.log` — 2 definitions, 4 theorems, all axiom-free; 4 facts closed (`clog_zero_left`, `clog_zero_right`, `clog_one_left`, `clog_one_right`); `clog_pos`/`log_le_clog` sized as a separate generalized-induction task |
