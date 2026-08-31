# ADR-1205: The bucket bug recurred one layer over; the depth spine stays a proposal

Status: accepted
Date: 2026-08-31
Index-summary: Third re-measurement of `curriculum.toml`'s `kernel_decls`
axis (ADR-1075, ADR-1140) since the depth proposal was written. Found the
same class of bug ADR-1140 had just fixed, recurring on a different node: the
`number-theory` bucket pattern's only Gauss's-lemma alternative was the
literal string `gauss_fold_injective`, so the 29-declaration
Gauss's-lemma-for-quadratic-reciprocity family that landed via ADR-1130 and
ADR-1150 (`gaussLemmaSignCount`, `gaussSignNeg`, `gaussFold`, `gaussNegCount`,
`gauss_neg_count_*`, `gauss_fold_*`, `secondSupplementaryLaw`,
`is_quadratic_residue*`, `pow_neg_one_of_*`, `half_ceil_parity`,
`leastResidue`) fell through to the `naturals`/`integers` catch-alls, silent
and invisible in the totals. A one-declaration twin (`Rat.sumRange_matSkip`,
from ADR-1155's Laplace layer) did the same to `linear-algebra`. Both fixed
by name, verified by name, not by watching the totals settle.
`number-theory`'s `kernel_decls` moves 108 → 137; `linear-algebra` 81 → 90;
four other nodes drift from ordinary landings in between (`naturals` 516→518,
`integers` 193→189, `rationals` 204→206, `propositional-logic` 64→65). Total
declarations 2,615 → 2,654, attributed 2,483 → 2,522, residual unchanged at
132 -- everything that landed attributed correctly once the buckets were
fixed. Confirms ADR-1075/ADR-1140's decision NOT to apply
`DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`'s ~30-node graph surgery
to `curriculum.toml` a third time: the consumer surface is unchanged, no new
rung has a self-checking scenario family, and no `status` field moved.
Index-status: accepted

Related: ADR-1075 (establishes the `kernel_decls` axis), ADR-1140 (the first
occurrence of this exact bug, on `linear-algebra`), ADR-1130 (Gauss's lemma),
ADR-1150 (the second supplementary law), ADR-1155 (Laplace row expansion)

Lane: `curriculum-spines`

## Context

The task: re-measure `curriculum.toml`'s `kernel_decls` axis after ADR-1130,
ADR-1150 and ADR-1155 landed real number-theory and linear-algebra content
since ADR-1140's measurement, find every consumer of the file, and either
apply the ~30-rung depth spine to the graph or say precisely why a smaller
change is right. This is the third lane on this exact brief; the first two
declined the graph surgery (ADR-1075, then ADR-1140 re-declined it after
fixing a bucket bug of its own).

## What re-measuring found: the same bug, one layer over

`kernel_declaration_projection` (release) fed through
`measure-curriculum-kernel-coverage.py` gave `number-theory = 108` --
unchanged from ADR-1140's pinned value, despite ADR-1130 (`Int.gaussLemmaSignCount`,
ADR-1130) and ADR-1150 (`Int.secondSupplementaryLaw`, ADR-1150) each landing
axiom-free theorems in the number-theory column hours earlier.

The cause is ADR-1140's own failure mode, recurring: the `number-theory`
bucket's Gauss's-lemma alternative was the literal string
`gauss_fold_injective`, added when `Nat.gauss_fold_injective_of_coprime` was
the only declaration of that shape. The new family spells itself two other
ways -- camelCase (`gaussLemmaSignCount`, `gaussSignNeg`, `gaussFold`,
`gaussNegCount`, `gaussCountBleClosedFormDisj`, `gaussTermModEq`,
`gaussSignProdEqPowNegOneOfCount`) and snake_case compounds
(`gauss_neg_count_*`, `gauss_fold_add_modeq_zero_of_sign_true`,
`gauss_fold_in_range`, `gauss_fold_modeq_of_sign_false`,
`gauss_fold_shift_injective_on`, `gauss_fold_shift_maps_into`,
`gauss_residue_two_eq_double_of_lt`) -- plus the QR-specific names
(`secondSupplementaryLaw`, `is_quadratic_residue`, `is_quadratic_residue_mul`,
`is_quadratic_residue_one`, `pow_neg_one_of_even`, `pow_neg_one_of_odd`,
`half_ceil_parity`, `leastResidue`). None of the 29 matched, so all 29 fell
through in bucket order to `naturals`/`integers`.

**The bucket order made this land safely rather than incorrectly**: because
`number-theory` precedes `divisibility-and-euclid` in the pattern table, this
bug could only ever under-count `number-theory` in favour of a later
catch-all, never mis-steal from a sibling destination. But the total stayed
exactly at 108 -- the same coincidence ADR-1140 already named: the existing
matches did not move, so nothing in the totals hinted anything was wrong.

`linear-algebra` had a matching one-declaration miss from ADR-1155's Laplace
row-expansion layer: `Rat.sumRange_matSkip` starts with `sumRange_`, not
`mat`, so it does not match any `mat(Id|Mul|Transpose|Skip|Minor|Inv2)`
alternative and fell to the `rationals` catch-all.

### The fix, and what it deliberately does not do

`gauss[A-Z]` -- any camelCase identifier starting `gauss` followed by a
capital letter -- catches every camelCase name above in one alternative,
because Rust's `declare_*` naming convention for this family is consistently
camelCase after the `gauss` root. Combined with explicit snake_case
alternatives (`gauss_neg_count`, `gauss_fold_`, `gauss_residue`) and the
QR-specific literals (`leastResidue`, `secondSupplementaryLaw`,
`is_quadratic_residue`, `pow_neg_one_of`, `half_ceil_parity`), every one of
the 29 now matches.

**The pattern deliberately does NOT match bare `gauss_lemma`.**
`Nat.gauss_lemma`/`Int.gauss_lemma` (declared in `nat_prelude/lcm.rs`) is a
*different* theorem -- the divisibility one, `gcd x y = 1 → x∣yz → x∣z` --
already correctly bucketed to `divisibility-and-euclid` by that node's own
literal `gauss_lemma` alternative. Same colloquial name ("Gauss's lemma"),
two unrelated statements; `gauss[A-Z]` cannot match `gauss_lemma` because the
character after `gauss` there is `_`, not a capital, so the two buckets stay
correctly separated. Verified by name: `Nat.gauss_lemma` and
`Int.gauss_lemma` both still classify as `divisibility-and-euclid` after the
fix.

`Rat.sumRange_matSkip` is added as an explicit literal alternative to
`linear-algebra`'s pattern for the same reason -- it names the specific miss
rather than widening the pattern generically and risking a false positive on
an unrelated `sumRange_*` lemma.

## Re-measured table

```sh
cargo run --release -p axeyum-lean-kernel \
  --example kernel_declaration_projection > /tmp/proj.tsv
python3 scripts/measure-curriculum-kernel-coverage.py /tmp/proj.tsv \
  --expect-attributed 2522 --require-node probability \
  --require-node linear-algebra --require-node number-theory
```

| node | ADR-1140 `kernel_decls` | new | drift | cause |
|---|---|---|---|---|
| propositional-logic | 64 | 65 | +1 | a new core declaration, unrelated to either bucket fix |
| naturals | 516 | 518 | +2 | net of +29 lost to the `number-theory` fix and +31 landed since ADR-1140 |
| integers | 193 | 189 | −4 | net of −9 lost to the `number-theory` fix and +5 landed since ADR-1140 |
| rationals | 204 | 206 | +2 | net of −1 lost to the `linear-algebra` fix and +3 landed since ADR-1140 |
| number-theory | 108 | 137 | +29 | the Gauss's-lemma bucket fix (ADR-1130, ADR-1150 content, previously mis-filed) |
| linear-algebra | 81 | 90 | +9 | ADR-1155's Laplace layer, one declaration of which needed the bucket fix |
| *(every other node)* | unchanged | unchanged | 0 | |

Total declarations moved 2,615 → 2,654 (+39); attributed moved 2,483 → 2,522
(+39); residual stayed at 132 in the same three categories (30 legacy
`AxReal` axioms, the 94-declaration string package, 8 not-yet-bucketed
carrier/misc declarations) -- every declaration that landed since ADR-1140
attributed correctly once the buckets were fixed, nothing fell into the gap.

Every drift above was verified BY NAME against the corrected patterns (the
full per-name table is in the commit that lands this ADR's changes), not
inferred from the totals. This is ADR-1140's own caution, restated because
the second occurrence proves it was necessary: an unmatched item is absorbed
by a catch-all rather than reported, so a total that looks plausible is not
evidence nothing moved.

## Consumers checked

`grep -rl curriculum.toml scripts/ crates/ docs/`, filtered to code (not
docs-only prose hits), and each real consumer re-run against the corrected
file:

| consumer | reads from `curriculum.toml` | affected by this change? |
|---|---|---|
| `scripts/lib/graph_dispatcher.py` | `status`, `layer`, `area`, `title` | no -- none of those fields changed |
| `scripts/gen-import-backlog.py` | `layer`, `title` | no -- ran clean (194 rows, up from 166 purely from unrelated fact-ledger landings; reverted after confirming the diff carries no curriculum-node content) |
| `scripts/validate-foundational-concepts.py` | `title`, `layer`, `area`, `status`, `family`, `prerequisites`, `unlocks` | no -- ran clean, 138 rows |
| `scripts/gen-foundational-concepts.py` | `id`, `decidability`, `status`, `family`, `prerequisites`, `unlocks` (not `kernel_decls`) | no -- regenerated `artifacts/ontology/foundational-concepts.json`, zero-byte diff |
| `scripts/gen-foundational-dashboards.py` | derived from `foundational-concepts.json` | no -- regenerated, zero-byte diff |
| `scripts/check-curriculum-coverage.py` | scenario-pack coverage per node id | no -- exits 0, `CURRICULUM_COVERAGE|covered=19|...` unchanged |
| `scripts/check-graph-dispatcher.py` | composes `graph_dispatcher.py` with the dispatchable-frontier gate | no -- exits 0 (the pre-existing unrelated `G7` failure ADR-1140 noted has since cleared) |
| `scripts/validate-claims.py` | curriculum node id membership | no -- 104 claims, 0 errors |
| `crates/axeyum-scenarios/src/mathtour.rs` | `NODES` mirror has no `kernel_decls` field at all | no -- `cargo test -p axeyum-scenarios --lib mathtour::`, 6/6 pass, 104.20s, including `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` |
| `crates/axeyum-scenarios/src/misconception.rs` | curriculum node ids only | no -- ids unchanged |

`kernel_decls` is read by neither generator despite ADR-1140's table implying
otherwise for `gen-foundational-concepts.py` -- re-checked directly this pass
(`grep kernel_decls` on both generators returns nothing) and confirmed by a
zero-byte diff on both generated artifacts after a real re-run, which is
stronger evidence than the grep alone.

## Why the depth spine still does not land as graph surgery

Unchanged from ADR-1075/ADR-1140, restated because the task asked to
reconsider it a third time:

- The consumer surface (five scripts, the `mathtour.rs` Rust mirror and its
  graph-invariant tests, `foundational-concepts.json`) is real work distinct
  from a measurement fix, and nothing in this pass changed that scope.
- Most proposed rungs still have no self-checking scenario family. N11's
  frontier narrowed this pass (Gauss's lemma and the second supplementary law
  are now landed, general reciprocity is not) but narrowing a rung's content
  does not manufacture a `Family` for it, and landing it as `status =
  "covered"` would still fail
  `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` on
  sight.
- Nothing that landed since ADR-1140 is itself evidence the smaller path is
  insufficient -- if anything, a second recurrence of the exact same
  measurement bug is evidence FOR keeping this a measurement-correction task
  rather than mixing it with the larger and separably-schedulable surgery.

## Documents corrected

- `docs/curriculum/curriculum.toml` -- six `kernel_decls` values, the header
  measurement block (dated, with the new `--expect-attributed` figure and the
  mechanism of both bucket fixes), and the `is covered with 81` → `90`
  cross-reference near the top.
- `scripts/measure-curriculum-kernel-coverage.py` -- widened the
  `number-theory` and `linear-algebra` bucket patterns, with comments naming
  the specific declarations each fix catches and why `gauss_lemma` itself is
  deliberately excluded.
- `docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` -- a
  correction block, the N11 table row, and the linear-algebra section's
  attribution figure.
- `docs/curriculum/03-destinations/number-theory.md` -- two new rows in the
  "Proved in the kernel" table (Gauss's lemma, the second supplementary law)
  and a corrected "Still Lean-horizon" bullet: general reciprocity, not the
  whole subject, is what remains open.
- `docs/curriculum/03-destinations/linear-algebra.md` -- a correction
  paragraph with the new 90-declaration count and the `sumRange_matSkip`
  bucket-fix note.

## Consequences

- `curriculum.toml`'s node count (24), `status`, `family`, `prerequisites` and
  `unlocks` are all unchanged; only `kernel_decls` values and header/summary
  prose moved. `mathtour.rs`'s tests are unaffected by construction.
- `measure-curriculum-kernel-coverage.py`'s `number-theory` bucket now covers
  the full Gauss's-lemma-for-quadratic-reciprocity family without matching
  the unrelated divisibility `gauss_lemma`; `linear-algebra` covers
  `sumRange_matSkip`.
- The depth spine remains exactly what ADR-1075 and ADR-1140 left it: a
  proposal, with N11's open frontier narrower than the proposal's own
  unedited prose still implies in places not touched by this pass (its
  ~30-rung tables elsewhere are left as a dated measurement, per ADR-1140's
  own precedent for `graded-statement-families-number-theory-and-linear-algebra.md`).
- A fourth lane on this brief should still start by re-running the
  measurement and checking bucket attribution BY NAME before touching
  anything else -- this is now the second time doing so found a real,
  previously invisible bug, and there is no reason to expect the pattern
  table has stopped growing stale between now and then.
