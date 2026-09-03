# Lane: tactic-combinator — `decide` and a `Then`/`First` tactic combinator over `linarith`/`ring`/`simp`

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this session`, tactic-combinator,
2026-09-03).** `decide` (the fourth producer, `crates/axeyum-lean-kernel/
src/decide.rs`) and `tactic` (the `Then`/`First` combinator over
`decide`/`linarith`/`ring`/`simp`, `crates/axeyum-lean-kernel/src/
tactic.rs`) both landed, ADR-1589. `decide`: closes a CLOSED `Eq Nat`/
`Eq Bool`/`Nat.le`/`Nat.lt` goal by fuel-bounded `whnf` (`MAX_MAGNITUDE =
30`), 16 tests (10 accepted incl. kernel-checked declarations, 3 free-var
`NotClosed`, 1 fuel-exceeded `Undecidable` not a hang, 2 hand-built
corrupted terms rejected by the kernel). Found and fixed a real bug in
`decide` itself while retiring the tenth evaluation check: the kernel's
compact `Lit` numeral representation, not only `succ`/`zero` chains
(`Nat.pair`'s `Bool`-selected branch produces one, `Nat.avg`'s does not) —
`nat_value` now peels both. Ten `avg_pair_tests` hand `def_eq` positive
checks retired onto `decide` (test-mechanism retirement, reported
separately from the hand-proof ledger below).

`tactic`: `Tactic::{Decide,Linarith,Ring,Simp,Then,First}`, ℕ-only
(`D: NatOps` — ℤ/ℚ scoped out, each carrier's own non-generic combinators
are a different `Ctx` shape, recorded as a deliberate cut not a gap). One
entry point exposed from `simp` (`simp::nat::normalize`, its own commit).
13 tests: 5×`Then(Simp,Linarith)`, 3×`Then(Simp,Ring)` (each asserting
BOTH producers decline alone before showing `Then` succeeds), `First` on a
mix incl. total-failure aggregation, one corrupted-glue test (kernel
rejects a mistyped residue spliced through `glue_rel`).

**Eight** `nat_prelude` hand proofs retired via the combinator (target was
ten — a measured shortfall, not a rounding; two candidates found and
declined as unsafe/out-of-scope, see ADR-1589 for both). Cross-producer
running total: **62** hand proofs (ADR-1576 15, ADR-1581 +5, ADR-1580 10,
ADR-1582 +10, ADR-1586 14, this lane 8). Cost (`--release`,
`--example decide_and_tactic_cost`): `decide` 0.006–0.025 ms/term (no
search, cheapest producer in the crate); `Then(Simp,Linarith)` 1.1–1.3 ms,
tracking `linarith`'s own measured range (consistent with "the
combinator's cost is the sum of what it dispatches to"). `check-fact-
depends-derived.py --fix`: 11 facts gained the emitter's dependency edges;
`validate-facts.py`: 2742 facts, 0 errors.

Did not run: the full unbounded `cargo test --lib` sweep (killed by the
box's own resource limit partway through the `complex`/`creal` suites,
unrelated to this lane's changes — no failures observed before the kill;
CLAUDE.md's own rule is not to run this sweep, and `nat_prelude::`/
`decide::`/`tactic::` (both narrow and combined, 424 + 29 + 453 total
across the runs) are what the brief asked for and are green).

<!-- plan-section: landed-changes -->

| 2026-09-03 | tactic-combinator | status stub opened |
| 2026-09-03 | tactic-combinator | `a7d0dd2b0` `decide.rs` landed: fourth producer, 16 tests |
| 2026-09-03 | tactic-combinator | `8604a38c8` `simp::nat::normalize` exposed (one entry point, own commit) |
| 2026-09-03 | tactic-combinator | `f233cd15a` `tactic.rs` landed: `Then`/`First` combinator, 13 tests |
| 2026-09-03 | tactic-combinator | `aba17ace0` fix(decide): peel the kernel's `Lit` numeral, not only succ-chains |
| 2026-09-03 | tactic-combinator | `94274c800` ten `avg_pair_tests` evaluation checks retired onto `decide` |
| 2026-09-03 | tactic-combinator | `cf3e18b24` eight `nat_prelude` hand proofs retired via `tactic` |
| 2026-09-03 | tactic-combinator | `e9ec1d745` `decide_and_tactic_cost` example, `--release` numbers |
| 2026-09-03 | tactic-combinator | `c5c3d8e21` `check-fact-depends-derived.py --fix`, 11 facts, `validate-facts.py` 0 errors |
