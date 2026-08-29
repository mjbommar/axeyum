# 289 — the 96 MB Lean module for `14x + 21y = 5`

Lane: `diophantine-blowup`.

**Status: fixed, with a measured residual.** The immediate defect is a one-word
call-site bug and is landed. The Diophantine route's module size is still
superlinear in the coefficients, which is a separate, bounded piece of work
written up below rather than papered over.

---

## Step 0 — reproduced standalone, before reading any code

    target/release/examples/lean_hypothesis_binding_dump \
      artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2

    2.24 s wall, stdout = 96,297,506 bytes (91.8 MiB)
    stderr: BINDING_DUMP|...|fragment=Diophantine|assertions=1|indices=0

Independently confirms the finding lane's number.

## Where the size came from — measured, not suspected

The module is 234 lines. **One of them is 96,155,365 bytes — 99.85 % of the
file**: line 232, the body of `theorem axeyum_refutation : False :=`. The
next-largest line is 14,183 bytes. Not a diffuse blowup; a single proof term.

Hash-consing that one line back into a DAG (`scratchpad/dio-profile.py`, an
explicit-stack tokeniser over the 10.9 M-token line) gives the answer:

| | |
| --- | --- |
| distinct nodes in the term | **18,018** — 46 leaf, 17,972 application |
| printed as a tree | **96,155,363 bytes** |
| printed with full sharing (computed from the DAG) | **~967,245 bytes**, 99× smaller |
| most-repeated single distinct subterm | **169,184** occurrences |
| distinct app nodes occurring >10³ times | 291 |

Printed-byte attribution over that line, by occurrence count × own length:

    43,480,584  leaf `axeyum.reconstruct.dio.x._1`
    20,578,860  leaf `axeyum.reconstruct.dio.x._0`
    17,093,174  leaf `Int.add`
     9,767,528  `Int.add` application syntax
     1,705,104  leaf `Int.zero`

So **the dominant term is not any part of the argument — it is the tree
expansion of a small DAG.** The proof is a chain of `Eq.rec` rewrites
(30,527 occurrences, over `Int.add_assoc`/`add_comm`/`add_zero`), and a Lean
`Eq.rec` reprints its subject term about four times per step (the type index,
the motive body, the two endpoints). Nest hundreds of those and you get 4^depth
without a single large number anywhere.

### Root cause: the renderer was called at the wrong entry point

`crates/axeyum-lean-kernel/src/lean_pp.rs:885` builds a share plan **only under
`compact`**:

    let shares = if compact {
        self.compact_share_plan(&[goal, proof], theorem_name, &at_consts)
    } else {
        LeanSharePlan::default()
    };

and `reconstruct_diophantine_to_lean_module` called `render_lean_module` — the
non-compact one. So no sharing was attempted at all.

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

## Slices for the residual, smallest first

1. **`combine_equalities` scales by `|λ|` repeated additions.**
   `crates/axeyum-solver/src/int_reconstruct/diophantine.rs:141-165`: the
   `for _ in 1..count` loop builds `λ·L` as `L + L + … + L` with an
   `eq_trans(congr_add_left, congr_add_right)` per copy. Coefficient magnitude
   therefore becomes proof *length*, and each step's rewrite chain then costs
   size in the length. A `mul`-based scaling (one `congr_mul_right` against an
   `Int` literal) replaces `O(λ)` steps with one. This is the single largest
   lever and is local to one function.
2. **The faithful linear form is unary too.** `lin_to_zexpr(combined_dense, 0)`
   renders `14x` as a 35-term sum of bare `x`/`y` atoms (visible in the rendered
   `dio.hyp._2` axiom), so the *normalizer* that follows has an `O(n²)`
   assoc/comm bubble to run over `n = Σ|coefficients|` terms rather than over
   the number of variables. Emitting `Int.mul (intlit 14) x` shrinks `n` from 35
   to 2 for this query.
3. **`Int` literals are unary as well** — `7` renders as
   `Int.add (… (Int.add Int.one Int.one) …)`, 32,758 `Int.one` occurrences in
   the pre-fix term. Same family as the kernel's unary-`Nat` finding
   (`CLAUDE.md`, "EVERY `Nat` NUMERAL THIS PRELUDE BUILDS IS UNARY"), and the
   same remedy applies: keep formed magnitudes small, or route through a literal.

Slices 1 and 2 are the same change seen from two sides and should be done
together; slice 3 is independent and smaller.

## Verification — all foreground, all completed

| check | result |
| --- | --- |
| pinned Lean 4.30.0 on the fixed 2.27 MB module | **exit 0, 11 s.** `#print axioms` = exactly `dio.hyp._2`, `dio.x._0`, `dio.x._1` — the three query-derived axioms, nothing else |
| `check-lra-hypothesis-binding.py --instance <the query> --expect bound` | `failures=0`, the instance BINDS (the corpus-floor errors are expected for a one-instance run) |
| `cargo check -p axeyum-solver --all-targets --features full` | ok |
| `cargo test -p axeyum-solver --features full --lib` | **1438 passed, 0 failed** |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | 1 passed, 0 failed |
| `--test diophantine_lean_reconstruct` | 5 passed, 0 failed (incl. `diophantine_module_checks_in_real_lean`) |
| `--test diophantine_evidence` | 4 passed, 0 failed |

Lean toolchain resolved with `scripts/check-lean-gate.sh --print-toolchain`:
`~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`, commit `d024af09`.

## Method notes

- The pre/post comparison uses **two binaries built from this worktree**, not
  the stale `target/release/` copy in the shared checkout (which predates
  `MAX_LEAN_MODULE_BYTES` and therefore returns the 96 MB module instead of
  declining it — that difference is what surfaced the correction above).
- Sizes are `wc -c` on stdout with stderr separated; the dumper writes its
  provenance line to stderr.
