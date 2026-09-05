# Lane: fib-backlog — close open facts in the natural-fibonacci / integer-fibonacci nursery families

<!-- plan-section: lane-status -->

**Your lane's block (`DONE this pass`, fib-backlog, 2026-08-28).** Closed
three of seven open `natural-fibonacci` facts. Zero of six `integer-fibonacci`
facts are reachable — `Int.fib : ℤ → ℤ` does not exist as a kernel
declaration (confirmed with `shape_search`, fresh build, `declarations=2000`);
every open Int fib fact, including the brief's stated keystone
`F:ml430-int-fib-add-181b6a2c`, quantifies over `Int.fib m`/`Int.fib n` for
genuinely negative `m, n : ℤ`, not `ofNat (Nat.fib n)`. `int_prelude/fibonacci.rs`
only ever builds `ofNat (Nat.fib n)` terms (used by `Int.fib_cassini`); it
never declares an `Int.fib` function. Building one (case-split on sign, with
the standard `fib(-n) = (-1)^(n+1) fib(n)` extension) is a genuine new-carrier
task, not a proof gap — the "unstatable, not unproved" case the brief
carved out. Did not attempt it.

Closed, forming one dependency chain:
- `Nat.fib_add_two_strictmono` — `StrictMono (fun n => fib (n+2))`.
- `Nat.fib_strictmonoOn` — `StrictMonoOn Nat.fib (Set.Ici 2)`, from the above.
- `Nat.fib_lt_fib` — `2 <= m -> (fib m < fib n <-> m < n)`, from the above
  plus the already-proved `Nat.fib_mono`.

Not attempted: `Nat.fastfib_eq` (needs a `Nat.fastFib` fast-doubling
<!-- absent: Nat.fastfib_eq, Nat.fastFib -->
definition that does not exist — same "needs a carrier" shape as the Int
family, smaller); `Nat.le_fib_self` / `Nat.le_fib_add_one` (a second,
independent chain — sized but not started, see below); the
`F:ml430-mutation-*` fib fact (an outcome-blind mutation of `fib_eq_zero`
that is FALSE as stated at `n=1`, so "closing" it means refutation, a
different task shape than proving the other twelve).

`Nat.le_fib_self : 5 <= n -> n <= fib n` is a second two-step-recursion
induction (pair `P(k+5) /\ P(k+6)` by ordinary induction on `k`, mirroring
`fib_add`'s device), sized at roughly the same effort as the strictmono
chain; `Nat.le_fib_add_one` is a two-line composition once it lands (small-`n`
concrete check for `n<5`, `le_fib_self` plus `le_add_right` for `n>=5`). Left
for the next lane rather than rushed.

<!-- plan-section: landed-changes -->

| 2026-08-28 | fib-backlog | `Nat.fib_add_two_strictmono`, `Nat.fib_strictmonoOn`, `Nat.fib_lt_fib` landed and kernel-checked (nat_prelude/fibonacci.rs); closed F:ml430-nat-fib-add-two-strictmono-c1e86d4d, F:ml430-nat-fib-strictmonoon-905810a9, F:ml430-nat-fib-lt-fib-3582b881 |
| 2026-08-28 | fib-backlog | confirmed `Int.fib` absent from the kernel (shape_search, fresh build, declarations=2000); all 6 open integer-fibonacci facts blocked on a missing carrier, not attempted <!-- was-absent: Int.fib --> |
