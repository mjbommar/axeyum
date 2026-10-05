# Lane: lean-c4-admission -- the feature works, the population does not move, and 217 of 361 rows sit behind axioms

<!-- plan-section: lane-status -->

**Lane block (`DONE -- ADR-1667 accepted; C4's first demand-gated feature built
and measured at +0 population survival`, lean-c4-admission, 2026-09-05).**

ADR-1662 measured that 361 of 756 pinned Mathlib statement mirrors are refused
because their own DEFINITION closure reaches a proof-bearing declaration, and
recommended extending the independently reconstructed substitution set over
seven constructive names. This lane built that, re-ran the census over the same
population, and found three things ADR-1662 could not have known.

## Headline

**390 statements crossed before. 390 cross after.** The five names addressed
fall to zero as first-reported blockers and the same 150 rows reappear behind
the next declaration in their own closure: exactly −150 / +150.

| | before | after |
| --- | ---: | ---: |
| admitted | 390 | **390** |
| `trusted-declaration-in-closure` | 361 | **361** |
| `Quot` as first blocker | 73 | **0** |
| `dif_pos` | 34 | **0** |
| `Nat.le_of_lt_add_one` | 24 | **0** |
| `And.left` | 12 | **0** |
| `Eq.subst` | 7 | **0** |
| `funext` | 0 | **62** |
| `eq_self` | 97 | **131** |
| `WellFounded.Nat.eager_eq` | 0 | **24** |
| `And.right` / `asymm` / `ne_eq` | 0 | **19 / 10 / 1** |

## What is actually behind the 361, now that the first layer is gone

| | rows | share |
| --- | ---: | ---: |
| axioms this kernel excludes (`propext` via `eq_self`, `funext`, `em`) | **217** | 60% |
| Lean's well-founded-recursion machinery (`Nat.mod_lt`, `WellFounded.Nat.eager_eq`) | **114** | 32% |
| ordinary constructive names still worth substituting (`And.right`, `asymm`, `ne_eq`) | **30** | 8% |

## The three findings

1. **`eq_self` is not constructive.** Its own Lean 4.30 closure reaches the
   `propext` AXIOM, so it belongs with `em`/`propext`. This re-confirms
   `docs/autogenesis/240-…` (2026-08-22) and `docs/autogenesis/295-…`
   (2026-08-27), which ADR-1662 lost. It is now a TEST, so the next census
   cannot re-recommend it.
2. **`Quot` needed no substitution.** `Kernel::add_quotient_package` already
   derives all four package types itself, so the gate was refusing a type
   former and its eliminators for a reason that only applies to proofs. This
   overturns doc 294's "`Quotient` never exempted, by hard rule" and doc 295's
   `permanent — Quot` row. `Quot.sound` is excluded at three independent
   points.
3. **C4's demand gate ranks by the wrong thing.** It picks a feature by
   FIRST-reported blocker, which on a layered frontier measures order in the
   stream rather than demand: `Quot` looked like 73 rows of demand and was
   worth 0.

## Two real-Lean suites are red, and both were measured red on `main` first

`cargo test -p axeyum-lean-import` is green on 26 of 28 integration suites and
all 150 lib tests (146 passed, 4 ignored). Two fail, both real-Lean gates on the
moved 4.34.0-rc1 pin:

- `real_lean_wire_differential::our_kernel_admits_nothing_the_real_lean_kernel_refuses`
  — `violations=2` of 307 (`level.max-kind:1322:max-to-imax`,
  `level.succ:1534:+1`)
- `thin_lean_adapter_goal_pack::the_eight_required_categories_are_each_graded_correctly_by_real_pinned_lean`
  — category `wrong_goal` graded `accepted`, expected `rejected`

Both re-run at the pre-change commit `26a245dc4` in an isolated snapshot and
**fail identically** (same counts, same violation ids, same assertion, pinned
toolchain present and `matches_pin=true` in both — neither is a skip). This lane
touches zero files in `axeyum-lean-kernel`, and neither suite reaches
`import_statement_ndjson`. Same family as the three gates `14-lean-lang.md`
records as red on `main` since the pin moved on 2026-09-03.

## Gates

`check-kernel-trusted-core.py` and `check-trust-closure.py` are byte-identical
before and after and were **already red on `main`** (`FAIL D: image_group.rs`
joined the core; a stale disclosure plus identity-map drift). The trusted core
is 257 functions / **5,534** lines both times — which also corrects ADR-1600's
5,526. `gen-lean-axiom-ledger.py --check` exit 0 both times.
`check-autogenesis-holdout-isolation.py` PASS both times, identical counts. The
published artifact lists 0 held-out ids of 205.

## Not done, deliberately

`Nat.mod_lt` (90 rows). Its own closure needs six more theorems (36 of its 42
are already substituted); a whole statement closure reaching it needs more
still. `And.right`/`asymm`/`ne_eq` (30 rows) are the measured next increment
and are left for the next lane, because the measurement above predicts they
move the frontier by 30 and survival by 0 again.

<!-- plan-section: landed-changes -->

| 2026-09-05 | lean-c4-admission | ADR-1662's recommended trusted-substitution extension, built and re-measured. `dif_pos`, `Eq.subst`, `And.left` reconstructed in `trusted_substitution`; `Nat.le_of_lt_add_one` in `nat_order_substitution`; the kernel's own quotient package exempted from the statement-isolation gate (overturning doc 294's hard rule). Each substitution carries a positive control and a negative control in which the reconstructed value is offered at a deliberately wrong type with every Rust-side guard bypassed. **Census re-run over the same 756 rows: 390 admitted before, 390 after** — the five names fall to zero as first blockers and the same 150 rows reappear behind the next declaration, exactly −150/+150. What is behind the 361 now: 217 rows behind axioms this kernel excludes, 114 behind Lean's well-founded-recursion machinery, 30 behind ordinary constructive names. `eq_self` (97, the largest blocker) is NOT constructive — its own Lean 4.30 closure reaches `propext`, re-confirming docs 240 and 295. Commits `88609630f`, `a43c7dc2d`, `afc01dbd4`; evidence `artifacts/measurements/statement-import-blocker-census-2026-09-05-after-c4.json` (carries `delta_against_baseline`) and ADR-1667. |
