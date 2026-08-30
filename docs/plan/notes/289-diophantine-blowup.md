# Notes: 289-diophantine-blowup

Detail moved out of [`../status/289-diophantine-blowup.md`](../status/289-diophantine-blowup.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`render_lean_module_compact` is documented as **semantically equivalent**: it
hoists repeated *closed* nodes to top-level definitions and never hoists
anything carrying loose de Bruijn or free variables. It is already what the
LRA (`reconstruct.rs:2124`, `:2148`), string-length, counterexample-cover and
quantifier-BV routes emit, so `check-lra-hypothesis-binding.py` already parses
this shape.

## The fix

One call site, `crates/axeyum-solver/src/int_reconstruct/diophantine.rs`
(`render_lean_module` → `render_lean_module_compact`), plus the reason at the
site and a re-pinned golden.

| | before | after |
| --- | --- | --- |
| `diophantine-gcd-obstruction-conflict.smt2` | 96,297,506 B | **2,268,010 B** (42.5× smaller) |
| render wall | 2.24 s | 0.79 s |
| `two_x_eq_one` golden body (`2x = 1`) | 1,142,012 B | **232,150 B** (4.9× smaller) |

## A correction to how the defect was described

The brief (and `docs/research/11-design-review/2026-08-29-two-gaps-the-gate-sweep-exposed.md`)
say the renderer "emits 96 MB, over **the checker's** 64 MB safety cap". The
64 MiB cap is **the solver's own**, `reconstruct::MAX_LEAN_MODULE_BYTES`
(`crates/axeyum-solver/src/reconstruct.rs:2276`), and it does not merely observe
the size — it *declines*. Measured at HEAD with a pre-fix binary built from this
worktree:

    lean_hypothesis_binding_dump: prove_unsat_to_lean_theory_module: malformed
    `lean_module_size` step: Diophantine produced a 96297506-byte Lean module,
    over the 67108864-byte cap. … Declining is the honest outcome
    -> exit 1, zero bytes on stdout

So the mechanism is: the solver **builds** the 96 MB module, refuses to return
it, the dumper exits nonzero, and `check_lra_hypothesis_binding.render_module`
turns that into `SystemExit(f"{instance}: the dumper failed: …")`. The 96 MB
figure is right and comes from the solver's own error text; there is no separate
checker-side cap. The cap was **not** raised, and nothing here argues it should
be — it is doing exactly its job.

## Is it a class? — yes, and the class is not closed by this fix

`artifacts/examples/math/number-theory-v0/smt2/` holds three queries; the other
two (`quadratic-nonresidue-mod7-bitblast-conflict`,
`bad-square-witness-mod7-bitblast-conflict`) render **no theory module at all**
— they route to `TermLevelEnum`, which emits only a structural attestation. So
this directory has exactly one Diophantine module and it is the one that broke.

The interesting measurement is synthetic. `a·x + b·y = c` with `gcd(a,b) ∤ c`,
rendered **after** the fix:

| a, b, c | compact module bytes |
| --- | --- |
| 2, 4, 1 | 218,478 |
| 6, 9, 5 | 666,950 |
| 14, 21, 5 | 2,268,010 |
| 22, 33, 5 | 7,168,617 |
| 30, 45, 5 | 16,851,112 |
| 38, 57, 5 | 32,968,627 |
| 50, 75, 5 | **72,595,011 — over the cap, declined** |

Roughly cubic in the coefficient (a 2.7× coefficient increase costs 14.5× the
bytes), for an argument whose *content* is one divisibility fact at every row.
The fix bought about 42× — three coefficient doublings — and no more.

**This is the honest residual and it is a decomposition, not a one-liner.**

### What drives the residual — measured, and it is NOT what I first wrote

Counting inside the compact modules (`/usr/bin/grep -o`, and `^def ` for the
hoisted bindings):

| a, b | bytes | `Int.one` | `Int.add` | top-level `def`s |
| --- | --- | --- | --- | --- |
| 2, 4 | 218,478 | 216 | 767 | 763 |
| 6, 9 | 666,950 | 630 | 2,419 | 4,712 |
| 14, 21 | 2,268,010 | 233 | 8,594 | 18,463 |
| 22, 33 | 7,168,617 | 273 | 26,782 | 60,317 |

`Int` literals in this reconstruction context **are** unary — `mk_intlit`
(`crates/axeyum-solver/src/int_reconstruct.rs:264`) is
`for _ in 1..count { acc = mk_add(acc, unit) }`, and the pre-fix tree carried
32,758 `Int.one` occurrences. But **after compaction the unary literals are
shared away and stop mattering**: `Int.one` stays in the low hundreds across a
33× byte range and does not even grow monotonically. So the unary-literal
family (`CLAUDE.md`, "EVERY `Nat` NUMERAL THIS PRELUDE BUILDS IS UNARY") is
*not* the driver here, and a lane sent at it would find nothing.

What grows is the **number of distinct proof nodes** — 763 → 60,317 hoisted
definitions, i.e. proof *length*, roughly quadratic-to-cubic in the coefficient.

## Slices for the residual, smallest first

1. **`combine_equalities` scales by `|λ|` repeated additions — this is the
   lever.** `crates/axeyum-solver/src/int_reconstruct/diophantine.rs`, the
   `for _ in 1..count` loop (`count = lambda.unsigned_abs()`) builds `λ·L` as
   `L + L + … + L` with an `eq_trans(congr_add_left, congr_add_right)` per copy.
   Coefficient *magnitude* becomes proof *length*, and the normalization that
   follows is then quadratic in that length. `IntReconstructCtx::congr_mul_right`
   already exists (`int_reconstruct.rs:468`) and `kernel_expr_to_zexpr` already
   recognises `ZExpr::Mul`, so `h : L = R  ⟹  λ·L = λ·R` is one step and the
   normalizer can consume it.

   **The trap to check first**: `congr_mul_right` needs the literal `λ` as a
   kernel term, and `mk_intlit` builds it as a unary tower, so the normalizer
   may distribute it straight back into `|λ|` copies. Measure whether
   `normalize`'s `ZExpr::Mul` arm keeps a literal factor symbolic before
   committing to this shape.

2. **The faithful linear form is unary too.** `lin_to_zexpr(combined_dense, 0)`
   renders `14x` as a 35-term sum of bare `x`/`y` atoms (visible in the rendered
   `dio.hyp._2` axiom), so the normalizer bubbles over `n = Σ|coefficients|`
   terms rather than over the number of *variables*. Emitting
   `Int.mul (intlit 14) x` takes `n` from 35 to 2 for this query. Same shape as
   slice 1 seen from the term side; they should land together.

3. **A binary `Int` literal representation.** Independent of 1 and 2, and by the
   table above it buys little on its own *after* compaction — record it, do not
   prioritise it.

## Verification — all foreground, all completed

| check | result |
| --- | --- |
| pinned Lean 4.30.0 on the fixed 2.27 MB module | **exit 0, 11 s.** `#print axioms` = exactly `dio.hyp._2`, `dio.x._0`, `dio.x._1` — the three query-derived axioms, nothing else |
| `check-lra-hypothesis-binding.py --instance <the query> --expect bound` | `failures=0`, the instance BINDS (the corpus-floor errors are expected for a one-instance run) |
| **the FULL `check-lra-hypothesis-binding.py --no-build`** | ran to completion in **36 min**, `rc=1`, `instances=135 … failures=133`. **Not green — see below.** |
| `cargo check -p axeyum-solver --all-targets --features full` | ok |
| `cargo test -p axeyum-solver --features full --lib` | **1438 passed, 0 failed** |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | 1 passed, 0 failed |
| `--test diophantine_lean_reconstruct` | 5 passed, 0 failed (incl. `diophantine_module_checks_in_real_lean`) |
| `--test diophantine_evidence` | 4 passed, 0 failed |

Lean toolchain resolved with `scripts/check-lean-gate.sh --print-toolchain`:
`~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`, commit `d024af09`.

### The gate does not go green, and the reason is documented in its own source

Full run after the fix:

    LRA_HYP_BINDING|instances=135|hypotheses=38|mutants_caught=133|…|failures=133

**The diophantine instance appears nowhere in the failure list** (`grep -c
diophantine` over the log = 0), which is the whole of this lane's claim on the
gate. The 133 are the `Real` → `CReal` carrier migration, and
`scripts/check-lra-hypothesis-binding.py:316-323` already states the number:

> THAT RUN IS FROM BEFORE `a6ee37c6a`. On HEAD `570b5c738` the same sweep
> reports **133 FAILURES** and it is not this checker's doing: 107 instances now
> render `axeyum.reconstruct.lra.x._N : CReal` where the carrier table expects
> `Real`, 10 render `Int` under the same prefix, and 19 structural modules
> changed shape. … Migrating it is the reals lane's call, not a loosening this
> lane may make.

So the state change this lane produced is exactly:

| | before | after |
| --- | --- | --- |
| gate outcome | `SystemExit`: the dumper exits 1 on the diophantine instance, **the run aborts and reaches no verdict at all** | runs to completion, reports its documented 133 |
| diophantine instance | crashes the run | binds, `failures=0` in isolation |

**The crash was hiding the whole verdict, not one row.** Nobody had seen this
sweep's summary line since the carrier migration, because the run died before
producing it.

Fixing the 133 is a carrier-vocabulary migration in the checker, explicitly
reserved to the reals lane by the comment above, and is **not** this lane's to
make. It is the honest reason the gate is red, and it is red at the same number
it was documented at.

## Method notes

- The pre/post comparison uses **two binaries built from this worktree**, not
  the stale `target/release/` copy in the shared checkout (which predates
  `MAX_LEAN_MODULE_BYTES` and therefore returns the 96 MB module instead of
  declining it — that difference is what surfaced the correction above).
- Sizes are `wc -c` on stdout with stderr separated; the dumper writes its
  provenance line to stderr.
