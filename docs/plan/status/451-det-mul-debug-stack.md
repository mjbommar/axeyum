# Lane: det-mul-debug-stack — the push-blocking debug stack overflow in `det_mat_mul_computes_at_concrete_matrices`

<!-- plan-section: lane-status -->

**DONE, det-mul-debug-stack, 2026-09-03.** `scripts/lane-push.sh` runs
`cargo test --workspace --lib` in DEBUG as an early battery step, and on `main`
`rat_prelude::det_mul_tests::det_mat_mul_computes_at_concrete_matrices`
(ADR-1543) aborted there with SIGABRT while passing `--release`. **It was a
bounded requirement that had grown, not a divergent term, and the cliff was one
`def_eq`.** Fixed by the documented remedy — keep the formed magnitude small —
with every asserted number unchanged. `40ee238ca`, `d466758bd`.

**The requirement, measured from outside the process.** An overflow aborts, so
it cannot be observed in-process; the test binary was run under varying
`RUST_MIN_STACK` instead. Before: aborts at 2,097,152 B (the default a `#[test]`
thread gets), passes at 4,194,304 and every larger power of two, 181 s each
time. After: passes at 2,097,152, still aborts at 1,048,576.

**Bisecting WITHIN the test named the cliff exactly.** Each block alone at
2 MiB:

| block | result | wall |
| --- | --- | ---: |
| prelude build alone | ok | 16.2 s |
| 1×1 `det ([[3]]·[[5]]) = 15` | ok | 16.5 s |
| 1×1 `15 ≠ 16` | ok | 16.0 s |
| 2×2 `det (A·B) = 4` | **ABORT** | 34.8 s |
| 2×2 `det A · det B = 4` | ok | 16.6 s |
| 2×2 `det A = −2`, `≠ +2` | ok | 15.9 s |
| 2×2 `det (A·B) ≠ 5` | **ABORT** | 35.2 s |
| 2×2 the instantiated theorem's equation | ok | 16.2 s |

Only `det (A·B) 2` is expensive, and it is the unary-numeral cost `CLAUDE.md`
documents: `A·B = [[19,22],[43,50]]` and the determinant forms `19·50 = 950`, a
950-deep `succ` tower. `det A · det B` forms nothing bigger than 4, and the
1×1 case nothing bigger than 15; both are free. The theorem instantiation is
free too — its two sides are the same `ExprId`.

**The fix keeps every number the test asserts.** `B` becomes `[[0,1],[2,1]]`,
determinant `−2` again, so `det A = det B = −2`, `det (A·B) = 4`, the `+2` / `5`
controls and the expansion's `1·4·(−2) + 2·3·(+2) = −8 + 12 = 4` are all
unchanged. Largest magnitude formed 950 → 28; the test goes 181 s → 16 s, which
is the prelude build alone.

**`det_mat_mul_expand_computes_over_the_whole_function_space` was a second
casualty the first abort hid** — it computes the same `det (A·B) 2` and aborted
identically. That is exactly the trap `artifacts/kernel-stack-envelope.tsv`
records: an overflow aborts the process, so only the FIRST affected test is
named. Same fixture change; its documented arithmetic is unchanged because the
row-swapped `[[2,1],[0,1]]` has determinant `+2` just as `[[7,8],[5,6]]` did.

**One control here could not fail, and is replaced.** The doc comment claimed
the determinant comparison would catch "a transposed index inside `Rat.matMul`
or `Rat.det`". It cannot: `det Aᵀ = det A`, so `A·Bᵀ`, `Aᵀ·B` and the double
swap all still have determinant 4 and the test passed. The product's four
entries are now read out directly — `A·B = [[4,3],[8,7]]` against
`A·Bᵀ = [[2,4],[4,10]]` and `Aᵀ·B = [[6,4],[8,6]]`, separated at `(0,0)` by two
explicit negative controls — and `det B = −2` / `det B ≠ +2` are asserted
directly rather than inferred from the product. Both bodies now also run on
`crate::on_a_deep_stack`, because 2,097,152 is EXACTLY the default and a passing
measurement with no margin is the shape that once let one `creal` declaration
stop the axiom-freedom guard from running.

**Non-vacuity by mutation, in this isolated worktree.** `B`'s second row
`[2,1] → [3,1]` (determinant `−3`) kills exactly these two tests and nothing
else in the module. A subject-side mutant (dropping the `neg` in `Rat.altSign`)
kills them too, but at the prelude build, since `altSign_succ` closes by
`Eq.refl` — so it does not demonstrate the evaluation table.

**`scripts/check-kernel-stack-envelope.sh --check` was RED on `main` in BOTH
profiles and nobody had run it.** Five rows had outgrown their pin; every
replacement is the measured minimum from `--measure`, so none is a divergent
term, and `--check` re-demonstrates the abort one power of two below each:

| profile | prelude | was | now |
| --- | --- | ---: | ---: |
| debug | `rat` | 1,048,576 | 2,097,152 |
| release | `rat` | 131,072 | 262,144 |
| release | `nat` | 65,536 | 131,072 |
| debug | `integer` | 262,144 | 524,288 |
| debug | `cpoint` | 33,554,432 | 67,108,864 |

`rat`'s debug row is now EXACTLY the 2 MiB a spawned thread gets, so **every
`#[test]` that calls `build_rat_prelude` on its own thread has zero margin.**
The crate is green today, but the next `rat` declaration of any depth will
abort something and will name only the first casualty. `DEEP_STACK_BYTES`
(256 MiB) is still 4× the new `cpoint` debug row.

**Other cliffs: none.** Rather than probe the `det` / `rowEchelon` / `rank` /
`sumMaps` / `prodRange` instantiations one at a time, the whole crate was run in
DEBUG — `cargo test -p axeyum-lean-kernel --lib`, **1,498 passed, 0 failed,
1,783.66 s**. Every concrete instantiation in the crate now runs in debug
without aborting.

**Verification.**

| check | result |
| --- | --- |
| `--lib` DEBUG, whole crate | 1,498 passed, 0 failed, 1,783.66 s |
| `--lib rat_prelude::` DEBUG, `--test-threads=4` | 239 passed, 0 failed, 763.01 s |
| `--release --lib rat_prelude::det_mul_tests` | 6 passed, 0 failed, 17.01 s |
| `scripts/check-kernel-suites.sh` | **exit 0**, 32 suites, 193 tests, every one `ok`, none INERT |
| `scripts/check-kernel-stack-envelope.sh --check`, `rat`, both profiles | exit 0, each with the required observed failure below the pin |
| `clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | clean |
| `rustfmt --edition 2024` on the touched file | clean |

**Two things a later lane should know, stated as precisely as the positives.**

- **`scripts/check-kernel-suites.sh` has no `--lib` flag; `--lib` is the
  DEFAULT and the flag is `--no-lib`.** A brief that says "run it with `--lib`"
  gets `exit 2, unknown argument`. `--no-lib` was run here (32 integration
  suites, exit 0) and paired with the separate whole-crate `--lib` sweep above,
  which is the same content the bare form would run and is how `hooks/pre-push`
  splits it.
- **`python3 scripts/check-absence-claims.py` is RED on `main` and this lane
  did not touch it.** 2 EXPIRED claims (`docs/plan/status/277-cas-multivariate.md:129`
  `Rat.prodRange`; `docs/plan/status/316-queue-sweep.md:50` `Nat.factorization`)
  and 168 bare unexpirable claims against a budget of 122, all in other lanes'
  status files, design-review notes and `creal/` sources. Not fixed here —
  every site belongs to another lane's area.

**Projection: no diff, structurally.** The only code change is inside
`#[cfg(test)] mod det_mul_tests;`, and `kernel_declaration_projection` builds
its preludes from non-test code, so it cannot move. Confirmed the projection
still builds: 3,095 distinct kernel declarations.

<!-- plan-section: landed-changes -->

| 2026-09-03 | det-mul-debug-stack | `40ee238ca` — the ADR-1543 concrete-matrix evaluation test aborted the DEBUG `--workspace --lib` push step (SIGABRT) while passing `--release`. Bisected from outside the process: a BOUNDED requirement, 4 MiB against the 2 MiB a `#[test]` thread gets. Bisected WITHIN the test: the single `def_eq (det (A·B) 2) 4` is the cliff, because `A·B = [[19,22],[43,50]]` forms `19·50 = 950` as a unary `succ` tower; `det A · det B` and the 1×1 case form nothing bigger than 15 and are free. `B` shrinks to `[[0,1],[2,1]]`, determinant `−2` again, so every asserted number is unchanged and the largest magnitude formed goes 950 → 28: 181 s → 16 s, which is the prelude build alone. `det_mat_mul_expand_...` was a second casualty the first abort hid and got the same change. One control that could NOT fail is replaced — `det Aᵀ = det A`, so no transposition is visible in the determinant; the product's four entries are now read out with `A·Bᵀ` and `Aᵀ·B` asserted apart at `(0,0)`. Mutation-checked: `[2,1] → [3,1]` kills exactly these two tests. |
| 2026-09-03 | det-mul-debug-stack | `d466758bd` — `check-kernel-stack-envelope.sh --check` was RED on `main` in BOTH profiles with nobody running it. Five rows re-derived by `--measure` and raised: debug `rat` 1,048,576 → 2,097,152, release `rat` 131,072 → 262,144, release `nat` 65,536 → 131,072, debug `integer` 262,144 → 524,288, debug `cpoint` 33,554,432 → 67,108,864. All bisect to a passing power of two, so none is a divergent term. `rat`'s debug row is now exactly the 2 MiB a spawned thread gets — zero margin for every `#[test]` that builds it on its own thread. |
