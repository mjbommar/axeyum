# ADR-1140: The depth spine stays a proposal; re-measure and fix the two rungs that already landed

Status: accepted
Date: 2026-08-31
Index-summary: Re-measured `curriculum.toml`'s `kernel_decls` axis
(ADR-1075) against the current tree and found a real bug, not just drift: the
`linear-algebra` bucket in `measure-curriculum-kernel-coverage.py` matched
`det2`/`det3` literally, so ADR-1120's general-`n` determinant
(`Rat.det`, `matSkip`, `matMinor`, `altSign`, `matInv2*`) fell through to the
`rationals` catch-all -- 22 declarations mis-attributed. Fixed the pattern,
re-measured (2,615 distinct declarations, 2,483 attributed, same 132
residual), and corrected six drifted `kernel_decls` values
(`naturals` 512→516, `integers` 186→193, `rationals` 211→204,
`divisibility-and-euclid` 151→153, `number-theory` 107→108,
`linear-algebra` 59→81). Confirms ADR-1075's decision NOT to apply
`DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`'s ~30-node graph surgery
to `curriculum.toml` this pass either -- the consumer surface (5 scripts, the
`mathtour.rs` Rust mirror and its graph-invariant tests, `foundational-concepts.json`)
is real work distinct from a measurement fix, and most proposed rungs have no
self-checking scenario family, so adding them as `covered` nodes would violate
`covered_nodes_have_a_family_realized_by_a_self_checking_scenario` on sight.
Instead corrects the two proposal rungs (N10 Euler's theorem, L7 the
general-`n` determinant) that landed axiom-free the same day the proposal was
written, in both the proposal document and the `number-theory.md`/
`linear-algebra.md` destination pages, which had independently gone stale on
the same two facts.
Index-status: accepted

Related: ADR-1075 (establishes the `kernel_decls` axis and the
`measure-curriculum-kernel-coverage.py` tool this ADR fixes a bug in),
ADR-1082 (adds the `probability` node), ADR-1110 (`Int.euler_totient_theorem`),
ADR-1120 (`Rat.det` at general `n`)

## Context

The task: re-measure `curriculum.toml`'s `kernel_decls` axis (ADR-1075) after
two theorems landed the same day it was pinned, find every consumer of the
file, and either apply `DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`'s
~30-rung spine to the graph or say precisely why a smaller change is right.

## What re-measuring found: a real bug, not just drift

Running `kernel_declaration_projection` fresh and feeding it through
`measure-curriculum-kernel-coverage.py` gave `linear-algebra = 59` --
unchanged from the stale pinned value, despite ADR-1120 having landed 13 new
`declare_*` functions and dozens of declarations (`Rat.det`, `det_zero`,
`det_succ`, `det_one`, `det_eq_det2`, `det_eq_det3`, `det_eval_*`, `matSkip`,
`matMinor`, `altSign`, `matInv2*`) hours earlier.

The cause: the script's `linear-algebra` bucket pattern was
`^Rat\.(det2|det3|dotN|mat(Id|Mul|Transpose)|cramer|inv2_|mul_adj2_)`, written
before the general-`n` determinant existed. `Rat.det` (bare), `Rat.det_one`,
`Rat.matSkip`, `Rat.matMinor`, `Rat.altSign` and `Rat.matInv2*` all start with
prefixes the pattern doesn't cover, so none of them matched -- and because
bucket order falls through to the `rationals` catch-all (`^Rat\.`) when
nothing more specific matches, all 22 were silently counted as `rationals`
instead. `linear-algebra`'s true count landed at exactly the pinned value by
coincidence: the pattern's own matches (dotN, matId/Mul/Transpose, cramer,
inv2_, mul_adj2_) hadn't moved, so the bug was invisible without diffing
declaration-by-declaration against the pattern.

This is precisely the failure `measure-curriculum-kernel-coverage.py`'s own
comments warn about ("the exact empty-grep-as-negative-result trap"), arriving
a second time on the very rung ADR-1075's depth-proposal companion document
names as the linear-algebra keystone. Fixed by widening the pattern to
`^Rat\.(det|dotN|mat(Id|Mul|Transpose|Skip|Minor|Inv2)|altSign|cramer|inv2_|mul_adj2_)`.

## Re-measured table

`cargo run --release -p axeyum-lean-kernel --example kernel_declaration_projection`
against the current tree (post ADR-1110, ADR-1120), through the fixed script:

```
python3 scripts/measure-curriculum-kernel-coverage.py <projection.tsv> \
  --expect-attributed 2483 --require-node probability \
  --require-node linear-algebra --require-node number-theory
```

| node | old `kernel_decls` | new | drift |
|---|---|---|---|
| naturals | 512 | 516 | +4 |
| integers | 186 | 193 | +7 |
| rationals | 211 | 204 | −7 |
| divisibility-and-euclid | 151 | 153 | +2 |
| number-theory | 107 | 108 | +1 |
| linear-algebra | 59 | 81 | +22 |
| *(every other node)* | unchanged | unchanged | 0 |

Total declarations moved 2,586 → 2,615 (+29); attributed moved 2,454 → 2,483
(+29); the six drifts sum to exactly +29, confirming the reconciliation.
Residual stayed at 132 in the same three categories (30 legacy `AxReal`
axioms, the 94-declaration string package, 8 not-yet-bucketed carrier/misc
declarations) -- nothing new fell into the gap, everything landed in a
correct bucket once the pattern was fixed.

All six corrected values, plus the header's regeneration command and
`--expect-attributed` figure, are updated in `curriculum.toml`.
`artifacts/ontology/foundational-concepts.json` and the four generated
`docs/foundational-resources/generated/*.md` dashboards were regenerated
(`gen-foundational-concepts.py`, `gen-foundational-dashboards.py`) and pick up
the corrected `linear-algebra` summary and a pre-existing but never-applied
drift from the `probability` node's addition (23 → 24 curriculum rows).

## Consumers checked

`grep -rl curriculum.toml scripts/ crates/ docs/` and read each script
consumer (docs-only prose hits are not consumers):

| consumer | reads from `curriculum.toml` | affected by this change? |
|---|---|---|
| `scripts/lib/graph_dispatcher.py` | `status`, `layer`, `area`, `title` (never `kernel_decls`; never rereads `status` after loading, ADR-1075) | no -- none of those fields changed |
| `scripts/gen-import-backlog.py` | `layer`, `title` | no |
| `scripts/validate-foundational-concepts.py` | `title`, `layer`, `area`, `status`, `family`, `prerequisites`, `unlocks` (never `summary` or `kernel_decls`) | no -- ran clean, 138 rows |
| `scripts/gen-foundational-concepts.py` | full node incl. `summary` | yes, correctly -- regenerated and picked up the `linear-algebra` summary edit |
| `scripts/gen-foundational-dashboards.py` | derived from `foundational-concepts.json` | yes, correctly -- regenerated, also caught the pre-existing stale `probability` count |
| `scripts/check-curriculum-coverage.py` | scenario-pack coverage per node id | no -- exits 0, `CURRICULUM_COVERAGE\|covered=19\|...` |
| `scripts/check-graph-dispatcher.py` | composes `graph_dispatcher.py` with the dispatchable-frontier gate | **pre-existing, unrelated failure**: `G7 queue-below-floor` from `check-dispatchable-frontier.py`, about the mathlib-import dispatch queue, nothing to do with curriculum nodes or this change |
| `crates/axeyum-scenarios/src/mathtour.rs` | `NODES` mirror has no `kernel_decls` field at all | no -- 6/6 `mathtour::` tests pass unchanged, 53.46s |
| `crates/axeyum-scenarios/src/misconception.rs` | curriculum node ids for misconception tagging | no -- ids unchanged |
| `scripts/validate-claims.py` | curriculum node id membership | no -- ids unchanged |

## Why the depth spine still does not land as graph surgery

`DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` proposes an eleven-rung
number-theory spine and a nine-rung linear-algebra spine as new nodes. ADR-1075
already declined to apply it in the same pass as the measurement fix, for a
real reason restated here because the task explicitly asked to reconsider it:

- **The consumer surface is genuinely separate work from a measurement fix.**
  Adding ~30 nodes means new `prerequisites`/`unlocks` edges (which
  `graph_dispatcher.py` DOES read and rank on), new rows in
  `foundational-concepts.json` (hand-checked against `curriculum.toml` by
  `validate-foundational-concepts.py`'s per-field equality checks), and a
  parallel `NODES` array in `mathtour.rs` whose graph-invariant tests
  (`graph_is_acyclic_and_total`, `prerequisites_reference_real_nodes`,
  `topological_order_respects_prerequisites`) would need to pass against the
  same edges twice, by construction, since the TOML and the Rust mirror are
  independently authored.
- **Most proposed rungs have no self-checking scenario family.** N7′
  (factorization uniqueness restated), N9 (CRT as its own node), N11
  (quadratic reciprocity), L3 (span) and L9 (eigenvalues) name kernel content
  or a genuine gap, not a `Family` scenario. Landing any of them as `status =
  "covered"` would immediately fail
  `covered_nodes_have_a_family_realized_by_a_self_checking_scenario` --
  exactly the mistake ADR-1075 rejected for `calculus`. Landing them as
  `status = "planned"` (the `probability` precedent, ADR-1082) is defensible
  for a genuinely new subject with no existing node; it is a worse fit for
  rungs that are currently *content inside* `number-theory` and
  `linear-algebra`, since splitting them out changes what those two nodes'
  existing `prerequisites`/`unlocks` edges mean and needs the edge-level
  verification above to not silently break the two destinations that already
  work.
- **Two of the rungs the proposal named as blockers already landed as content
  inside the existing nodes**, which is direct evidence the smaller path is
  sufficient for what actually needed fixing: N10 (Euler's theorem) and L7
  (the general-`n` determinant) are both now proved, axiom-free, and both
  attribute correctly to `number-theory`/`linear-algebra` once the bucket bug
  above is fixed -- with zero graph surgery.

So this ADR does the same thing ADR-1075 did: correct the measurement, correct
the documents the measurement feeds, and leave the ~30-node proposal as a
proposal. A future task that specifically budgets the five-script-plus-Rust-
mirror consumer surface (not folded into a measurement-and-doc-correction task)
is the right shape for the graph surgery itself, should a scenario family for
one of the open rungs (N7′, N11, L3, L9) get built first and make `covered`
status honest for it.

## Documents corrected

Two rungs -- N10 (`Int.euler_totient_theorem`, ADR-1110) and L7 (`Rat.det` at
general `n`, ADR-1120) -- landed the same day
`DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` was written, so the
proposal called both the live frontier when both were already closed by the
time anyone read it again:

- `docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` -- a
  correction block at the top, and the N10/L7 table rows, the "live rungs"
  prose, and the linear-algebra keystone recommendation updated in place.
- `docs/curriculum/03-destinations/number-theory.md` -- added
  `Int.euler_totient_theorem` to the "Proved in the kernel" table; removed the
  stale "Euler's theorem ... absent" bullet from "Still Lean-horizon".
- `docs/curriculum/03-destinations/linear-algebra.md` -- rewrote the "Fixed
  size 2 and 3" bullet to lead with the general-`n` determinant, and replaced
  the closing "the remaining genuine gap is the determinant at general `n`"
  paragraph (itself only hours old) with the corrected 81-declaration count
  and the actual remaining gap (spectral theory).
- `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md`
  -- a top-of-file correction note pointing at the two stale row-1 entries
  (§2.2, §3.3) and at the two destination pages above for the maintained
  version; the 821-line body is left as a dated measurement rather than
  rewritten, since it was accurate the day it was written and rewriting it in
  place would cost more than this task's budget for a document nothing
  mechanically consumes.

## Consequences

- `curriculum.toml`'s node count, `status`, `family`, `prerequisites` and
  `unlocks` are all unchanged; only `kernel_decls` values, the header
  measurement comment, and the `linear-algebra` node's `summary` moved.
  `mathtour.rs`'s tests are unaffected by construction (same reasoning as
  ADR-1075).
- `measure-curriculum-kernel-coverage.py`'s `linear-algebra` bucket bug is
  fixed; a declaration named `Rat.det*`/`matSkip`/`matMinor`/`altSign`/
  `matInv2*` now attributes correctly instead of falling through.
- The depth spine remains exactly what ADR-1075 left it: a proposal, with two
  more of its rungs now landed as kernel content and correctly reflected
  everywhere the measurement is read from.
