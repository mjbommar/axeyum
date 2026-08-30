# Notes: 273-logic-excluded-middle

Detail moved out of [`../status/273-logic-excluded-middle.md`](../status/273-logic-excluded-middle.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. `Formula` AST (var/bot/and_/or_/imp over a `Nat` carrier) — **landed this
   lane**.
2. Inductive derivation relation `Provable : Formula -> Prop` (or
   context-indexed) encoding IPC natural deduction's rules — **not
   attempted**, genuine research/engineering sized comparably to this
   kernel's other multi-hundred-line prelude developments.
3. Generic `eval : Formula -> (Nat -> Nat) -> Nat` via `Formula.rec` — **not
   attempted** (this lane's countermodel evaluates the ONE closed instance
   directly in `Nat`, without the recursor, which is cheaper but does not
   generalize).
4. Soundness theorem (`Provable f -> forall valuations, eval f = top`) by
   induction on the derivation — **not attempted**, the real missing
   mathematical content.
5. A 3-element Gödel/Łukasiewicz Heyting-chain semantic countermodel
   (`meet3`/`join3`/`himp3`/`not3` as `Nat -> Nat -> Nat` definitions,
   `join3(1, not3(1)) = 1 != 2`) — **landed this lane**, as a kernel
   `Theorem` (`ipc_heyting_join_not_ne_top`), axiom-free
   (`Kernel::axiom_footprint` checked empty in-test).

**Combining 1+2+3+4+5 closes `F:excluded-middle-not-intuitionistic`** in the
same style as `CReal.evt_attained_max_decides_sign` /
`CReal.ivt_exact_root_decides_sign` (ADR-0603 row 2). Slices 2–4 are the
remaining gap and are the next lane's task; 1 and 5 are done and reusable.

**Landed as a NEW, honestly-scoped fact** (per the standing rule: do not
weaken the target fact's statement, land a genuinely different proposition
under its own id instead):
[`F:heyting-3-chain-refutes-excluded-middle`](../../../artifacts/facts/F-heyting-3-chain-refutes-excluded-middle.json) —
a purely SEMANTIC countermodel result (`proved`, `kernel-lean`,
`axiom_footprint: []`), which does **not** close
`F:excluded-middle-not-intuitionistic` (that stays `open`, with its `notes`
field updated to record this scoping and point here).

**File**: `crates/axeyum-lean-kernel/src/ipc_heyting.rs` (new module, does
not touch `nat_prelude/` or `creal/`). Registered in `lib.rs` with a 2-line
diff (`mod ipc_heyting;` + one `pub use`). 7 unit tests, all passing;
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean;
`rustfmt --edition 2024 --check` clean on both changed files;
`python3 scripts/validate-facts.py` reports 0 errors over 1950 facts
(up from 1949).

**Gotcha hit and worth recording**: building `Eq Nat lhs two_nat` with the
`Eq` universe parameter at `level_zero` (Prop) instead of `level_succ(zero)`
(Type, since `Nat` lives at `Sort 1`) produced
`TypeMismatch { expected: ExprId(0), got: ExprId(2) }` — exactly the
"a sort-shaped low `ExprId` means the kernel wanted a different SORT"
signature this file's Gotchas section already documents, isolated by
bisecting the four `declare_*` calls one at a time against a throwaway
`isolation_probe` test module (removed before the final commit).

**What the next lane needs**: build the `Provable` inductive relation (slice
2) over `crates/axeyum-lean-kernel/src/ipc_heyting.rs`'s `Formula` type —
assumption, `∧I`/`∧E1`/`∧E2`, `∨I1`/`∨I2`/`∨E`, `→I`/`→E`, `⊥E` — most likely
context-indexed (`Provable : List Formula -> Formula -> Prop`, needing a
`List`-shaped carrier the kernel does not have either — `Nat.Pair`-style
`Bool`-selected encoding, or another `add_recursive_datatype_family`, is the
likely route). Then slices 3–4. Do not attempt all of 2–4 in one sitting;
slice further if needed (e.g. land `Provable` and a handful of easy closure
lemmas about it before attempting soundness).
