# Lane: gauss-mapsinto-bound — Gauss's-lemma piece 2, MapsInto + shift wrapper

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, gauss-mapsinto-bound, 2026-08-31).** ADR-1015's
two-item sizing survived intact: exactly the range bound and the 0-indexed
shift wrapper, plus the one new arithmetic fact it named. Piece 2 is now
**complete**.

Landed this session (all axiom footprint 0, read from
`theorem_axiom_footprint`, one name per invocation):

- `Nat.div_succ_two_mul_eq_self : div (succ (mul 2 m)) 2 = m` — exactly
  ADR-1015's sketched route (`add_mul_div_left` at `(1, m, 2)` +
  `add_comm` bridge to `pp`'s `succ`-shape + `zero_add`). No surprises;
  matched the sizing almost line for line.
- `Nat.gauss_fold_in_range : gcd a pp = 1 → 0 < k → Le k m → And (0 <
  gaussFold pp a k) (Le (gaussFold pp a k) m)` — the `MapsInto` range
  bound. Route deviated from ADR-1015's guess in one place: rather than a
  `sub_le_sub_left`-shaped lemma (which does not exist in the tree), the
  upper bound in the negative branch goes through `sub_le_iff_le_add`'s
  reverse direction plus `add_le_add_left` — cleaner than what was sized.
- `Nat.gauss_fold_shift_maps_into` / `Nat.gauss_fold_shift_injective_on` —
  the 0-indexed shift wrapper (`σ(j) := pred (gaussFold pp a (succ j))`).
  Routine composition exactly as sized: `Lt i m` is defeq `Le (succ i) m`,
  matching `gauss_fold_in_range`'s hypothesis shape with no bridging lemma
  (confirmed, not just assumed); `succ_pred_of_pos` + `succ_injective`
  close the rest.
- Concrete instantiation test (`gauss_fold_range_bound_and_shift_wrapper_
  apply_at_pp_seven`) checking all four new declarations apply at
  `pp := 7, m := 3, a := 2, i := j := 0`, mirroring the existing `pp := 7`
  instance so the two tests' numerals cross-check each other.
- `theorem_names()` (`nat_prelude_tests.rs`) updated in the same commit as
  the declarations — `every_nat_declaration_is_checked_and_axiom_free`
  caught the omission on the first sweep, exactly as it is supposed to.

**Piece 2 is complete.** `Int.prodRange_permute`'s `InjectiveOn`/`MapsInto`
hypotheses are both satisfiable by the signed fold on `[0, m)` with no
separate bijection or partner-index construction, as ADR-0990/ADR-1015
predicted.

**What piece 3 needs, unchanged from ADR-0990/ADR-1015**: the product-
cancellation argument connecting `gaussNegCount` to `a^m mod pp` via
`Int.prodRange_permute`, plus the Nat/Int carrier bridge — genuinely
larger than pieces 1+2 combined, not attempted or re-sized this session.

Verification: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 259
passed, 0 failed (up from 258 at session start), including the
environment-derived coverage assertion and the new concrete test, verified
individually present via `--list` (not grepped from a log).
`theorem_axiom_footprint` run once per name: `div_succ_two_mul_eq_self`,
`gauss_fold_in_range`, `gauss_fold_shift_maps_into`,
`gauss_fold_shift_injective_on` — all footprint `0`.
`python3 scripts/check-autogenesis-holdout-isolation.py` — PASS,
`held_out=146`, checked before AND after, `artifacts/autogenesis/`
untouched. `cargo check -p axeyum-lean-kernel --lib` clean.
`scripts/lane-prepush-fmt.sh` run before the final commit.

**Note on clippy**: `cargo clippy -p axeyum-lean-kernel --all-targets -D
warnings` fails on PRE-EXISTING issues unrelated to this session's diff —
two lints in this file at lines that existed on `origin/main` before this
session (`(1..=m).filter(...).count() as u32`, `(a_bad * 1) % pp`, both in
the module's own `#[cfg(test)]` Python-cross-check block), plus dead-code
warnings in `nat_prelude_tests.rs` and a doc-comment typo in an unrelated
test file, none introduced here. Confirmed via `git show
878c285d9:crates/.../gauss_lemma.rs` (the commit this session started
from) — both flagged lines are present verbatim. Not fixed: out of this
lane's scope (shared files, other lanes' recent work), and fixing them
risks the exact multi-agent hygiene hazards CLAUDE.md warns about.

**Hardest step this session**: not the arithmetic fact (which landed
almost exactly as sized) but a carrier-mismatch bug the sizing could not
have predicted. `d.symm`/`d.trans`/`d.eq_motive`/`d.transport` are
hardcoded to the `Nat` carrier (per `NatOps`'s own implementation), and the
"not negative" branch of `gauss_fold_in_range` needed to derive a
contradiction from two `Bool`-typed hypotheses (`gaussSignNeg pp a k =
false` and an assumed `= true`). Using the Nat-typed `d.symm`/`d.trans` on
`Bool`-sorted values (`test`, `Bool.false`, `Bool.true`) built a
syntactically valid but ill-typed term, and it surfaced as an opaque
`TypeMismatch { expected: ExprId(3), got: ExprId(5726) }` deep inside the
whole-prelude build — the tiny `expected` id was the SORT-error tell
CLAUDE.md documents, but the ID pair alone did not localize which branch.
Localizing it needed `Kernel::infer_in` against an explicit `LocalContext`
(closing over the theorem's own arity fvars `m,a,k` plus the hypothesis
fvars, extracted via `Kernel::expr_node` pattern-matching `ExprNode::FVar`)
rather than the bare `Kernel::infer` this file's own module doc recommends
elsewhere — a bare `infer` on a subterm that still has legitimately-open
arity variables reports `UnboundFVar` on those instead of the real defect,
which is itself a trap worth naming: **a probe on an OPEN subterm inside a
`d.theorem` closure will misreport as `UnboundFVar` regardless of whether
the subterm is otherwise well-typed, because the arity variables are not
yet bound at that point in construction.** The fix, once localized, was a
one-line swap to the file's own pre-existing `d.bool_symm`/`d.bool_trans`.

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-mapsinto-bound | `Nat.div_succ_two_mul_eq_self`, `Nat.gauss_fold_in_range`, `Nat.gauss_fold_shift_maps_into` and `Nat.gauss_fold_shift_injective_on` land axiom-free in `nat_prelude/gauss_lemma.rs` -- completing Gauss's-lemma piece 2 (ADR-0970/ADR-0985/ADR-0990/ADR-1015). `Int.prodRange_permute`'s `InjectiveOn`/`MapsInto` hypotheses are now both satisfiable by the signed fold on `[0, m)`. Piece 3 (product cancellation, Nat/Int carrier bridge) is what remains, unchanged in size from ADR-0990/ADR-1015. |
