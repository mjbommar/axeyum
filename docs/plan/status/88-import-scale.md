# Lane: import-scale — the import corpus is now the environment itself

<!-- plan-section: lane-status -->

**Exported all of `Init`+`Std` (96,591 declarations) and all of Mathlib
(680,925), measured a seeded random sample of each, fixed the binding constraint
— kernel `Nat` literal arithmetic — and located the next one (`String`
literals: 52% of `Init`+`Std`, 79% of Mathlib)** (`WIP`, import-scale,
2026-08-15). Continues [`whnf-cache-key`](87-whnf-cache-key.md), whose 40/40
corpus had stopped measuring. Full write-up:
[`docs/formalized-math-2026-08/diary-import-scale.md`](../../formalized-math-2026-08/diary-import-scale.md).

**The corpus.** `lean4export` with no constant list dumps the whole environment:
`Init`+`Std` is 10.5M records / 96,591 declarations / 25 s / 552 MB, and Mathlib
v4.30.0 (`c5ea0035`, built on s5 from `lake exe cache get` in 77 s) is 680,925
declarations / 5.5 GB / ~4 min. Both under `/nas3/data/axeyum/lean-import-scale/`.
`scripts/lean-import-scale-census.sh` (new) samples that name list with a
recorded seed, exports each declaration's own closure, and censuses it under an
OS-enforced time and address-space bound — per stream, so a diverging declaration
costs one bucket instead of the run.

**The whole-environment stream cannot be censused in one pass, and the reason is
the first result.** Three minutes in, RSS was 22 GB and climbing; the process's
own `/proc/<pid>/fdinfo` offset was **frozen** at 0.4% of the file across a
minute in which it allocated another 3 GB. Stuck on one declaration, not slow —
`Nat.Linear.Expr.denote_toPoly_go`, which alone consumed 25 GB without answering.
A stream through the trusted gate has a third outcome besides admit and decline:
it can diverge, and a run that dies partway looks like a resource problem rather
than a located one.

**The constraint was literal `Nat` arithmetic.** The failing streams' literals
gave it away: `55296`, `57343`, `1114112`, `4294967296` — `Char`, `UInt*`,
`USize` and `Fin` are `Nat` under bounds like `2^32`, and this kernel had no rule
for `Nat.add` on literals, only `Nat.succ` folding. Reaching `2^32` by successor
steps is unbounded, not slow. `Kernel::reduce_nat_binop` is Lean's
`type_checker::reduce_nat` for the fourteen binary operations, arbitrary
precision, with Lean's totality conventions and Lean's `1 << 24` exponent bound.
`Nat.Linear.Expr.denote_toPoly_go` went from 25 GB/no answer to **clean in
0.04 s**; `Option.repr` from 8 GB exhausted in 95 s to the next wall in 0.05 s.

**Guards, because this widens definitional equality.** A `Definition` (never an
axiom or opaque), no universe parameters, exactly `Nat → Nat → Nat` or
`Nat → Nat → Bool`, and Lean's `Bool` (`[false, true]`, indices 0 and 1). Two
traps paid for: the type must be checked by *walking* the `Pi` layers, because
binder names are part of an interned node and the official export names them
(my first version compared ids, never fired, and the census was unchanged); and
the table must **look names up without interning them**, because name ids are
emitted in insertion order and minting `Bool.true` during a reduction renumbers
the whole subsequent export — `axeyum_built_prelude_round_trips` caught that.

**Our own preludes are untouched by mechanism, not by luck:** `build_logic_prelude`
declares `Bool` as `[true, false]`, which is not Lean's, so the table is refused
for every prelude-built environment and the 119-theorem `nat` inventory cannot
move. `tc_tests::the_reconstruction_prelude_is_not_accelerated` asserts all three
links of that argument.

**Controls, one clause at a time.** Rule off → 4 positives fail. Type check off,
kind check off, arity check off, `pow` bound off → each flips exactly one
negative test. The two `Bool`-order clauses are **individually redundant and
jointly load-bearing** — dropping either alone changes nothing, dropping both
flips the test. A one-line summary would have been wrong; the controls had to be
run separately to know which.

**The answers are checked by Lean.** `real_lean_nat_arithmetic_crosscheck` (new,
registered in the gate) generates its obligations *from this kernel's output* —
24 argument pairs including both totality conventions, truncated `sub`, `gcd`
with a zero, and values past `2^64` — and official Lean 4.30.0 accepts all 24.
Mutating `x % 0` from `x` to `0` makes Lean reject, so it discriminates. Floor
raised 105 → 107; measured 115.

**Distribution, 500 random `Init`+`Std` / 400 random Mathlib declarations:**
CLEAN 219 (43.8%) / 78 (19.5%); **UNSUPPORTED `literal-string-typing` 262
(52.4%) / 315 (78.8%)**; DECLINED 16 / 7; RESOURCE 3 / 0. Cascades separated:
265 declines → **6 distinct roots**, and 154 → **5** — of which four are the
same declarations. **Not one Mathlib-specific root blocker**: everything this
kernel refuses across a 400-strong Mathlib sample is in Lean's `Init`/`Std` core
(`Nat.bitwise._unary`, `Nat.Linear.*`, `Fin.*`). Category theory, measure theory,
affine geometry and functional analysis are in the clean set.

A fourth outcome class was also separated: some of the RESOURCE streams were
**stack overflow**, not memory. The census now runs on a 512 MB stack (what
`lean -s` does) — which fixed exactly **one** of the four; the other three run
longer, reach ~6.3 GB of heap and overflow that too. Runaway reduction, not
deep-but-finite. I had written "all four import in under two seconds" in that doc
comment before measuring the other three.

Next: **`String` literals**, sized in the diary against Lean's own call sites
(wire arm, `Lit::Str` typing behind a `String` bootstrap,
`string_lit_to_constructor`, the `whnf` and `def_eq` uses, the writer's
round-trip). Roughly 1.5× this lane's `Nat` work — one focused session. Note that
`String.ofList` is a *definition* in Lean 4.30, not a constructor, so the
expansion is δ-reducible; that is where a port goes wrong. It buys 52%/79% of
streams *reaching the next wall*, not 52%/79% clean — what is past strings for
those is unmeasured. Still open across four diaries: the toolchain re-pin.

<!-- plan-section: landed-changes -->

| 2026-08-15 | (pending) | Literal `Nat` arithmetic in the kernel (Lean's `reduce_nat`, 14 operations, guarded by a validated `Nat`/`Bool` bootstrap and a non-interning name lookup), with 15 new tests, guard-by-guard controls, and a real-Lean crosscheck generated from this kernel's own answers (gate floor 105 → 107, measured 115); `scripts/lean-import-scale-census.sh` censuses a seeded sample of the whole exported environment with roots separated from cascades; census example runs on a 512 MB stack and reports reader-refused streams as their own class. |
