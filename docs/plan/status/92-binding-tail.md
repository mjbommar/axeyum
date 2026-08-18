# Lane: binding-tail — the four verdicts are a partition, and each one can now fail in both directions

<!-- plan-section: lane-status -->

**66 instances were recording the weaker of two true statements, 4 more were
recording nothing at all, and the converse number could not be read** (`WIP`,
binding-tail, 2026-08-18).

Gate line, `python3 scripts/check-lra-hypothesis-binding.py` (~35 s), before →
after:

    instances=135 | structural=95  | anchored=10 | attested=9 | failures=0
    spine_assertions=541 | represented_assertions=296

    instances=135 | structural=102 | structural_anchored=66 | anchored=73
    anchored_nodes=1098 | attested=5 | failures=0
    spine_assertions=541 | represented_assertions=296 | undecomposable_spine=0

**Nothing was weakened to get any of it.** Every number that moved moved because
a check was added or a statement that was already true started being recorded.

**1. The overlap was measured and it is the largest class.** `structural` and
`anchored` answer different questions and the manifests were mutually exclusive
*by construction*, so nobody had ever run both binders over both lists. Doing it:
63 of the 95 `structural` rows also anchor — their query asserts the disequality
outright instead of leaving it a congruence conclusion — and 3 of the 10
`anchored` rows also bind structurally, because `(ite true x y)` is a four-node
term of the file. The dual class is 66, larger than the other three together.

The real change is not the class, it is that **every pin is now two-sided**:

    structural           binds structurally, and does NOT anchor        (32)
    structural-anchored  does BOTH                                      (66)
    anchored             anchors, and does NOT bind structurally         (7)
    attested             does NEITHER                                    (5)

The negative half is the half that does the work. Without it a class can only be
entered by hand and never left, so a stronger statement that becomes true stays
unrecorded forever and a class that stops describing its members stays green.
That is exactly how six `QfAbv`/`QfUf` instances sat pinned content-free while
they were structural all along; this is the same shape, one class over. It cuts
both ways now — a row pinned `structural` that *starts* anchoring **fails the
run**.

The dual verdict is deliberately **not** expressed as membership of both existing
manifests. It is its own file with its own two-sided pin, so an instance still
belongs to exactly one class and cannot pass on whichever half it happens to
satisfy.

**2. The 4 `FiniteArrayExtensionality` rows were never content-free.** The
certificate's `read_equalities` are the query's own `TermId`s and always were;
`reconstruct_finite_array_extensionality_to_lean_module` collapsed each
`(select a i)` into one opaque `atom._N` before rendering, so a module containing
every read of the file reached Lean saying nothing about any of them. Identical
defect and identical fix to the 89 `ArrayAxiom` rows earlier the same day, under
the same all-or-nothing node budget. 360 matched term nodes, and all four
corruptions of each are caught. They bind structurally and are correctly
**refused** the anchored pin: their refutation is `¬(r₁ ∧ … ∧ rₙ)`, and a negated
conjunction is not a fact about either conjunct.

Two checker changes were needed to see it, both narrower than they could have
been. `bind_structural` now collects the terms of every equality across a
`Not`/`And` tree, with the grammar **closed** at those three heads — `Or` and
`Iff` are refused, because a disjunction says something weaker and admitting it
would let a module state less while its terms went on matching. And
`bind_structural`'s search had **no node budget** and a static side ordering:
sixteen same-sized sides against sixteen same-sized candidates ran for minutes on
`smtextarrayaxiom3`. It now picks the most constrained side at each step and
carries a 200k-node budget whose verdict is **distinct from a refusal** — a
search that gave up must read as neither a pass nor a caught defect.

**3. The converse number could not be read, and now it can.**
`represented_assertions=296` of `spine_assertions=541` was published without the
one fact that makes it interpretable: whether the 245 unrepresented rows are a
property of the refutations or a blind spot in the checker. A row this Python
parser cannot decompose is unrepresentable whatever the module renders, so it
arrives as a *lower* `represented` and reads as the modules resting on less of
the query. One number, shrinking for two opposite reasons, with no way to tell
which. Measured across all 135 bound instances: **zero** of the 541 rows are in
that state, so 296/541 is a fact about the refutations — they rest on 296 rows
and Lean derives `False` from those alone. `undecomposable_spine` is reported and
a nonzero count **fails the run**.

The 296 itself was computed the cheap way. An overlap count lets one hypothesis
stand for several rows, so three assertions entailing a common atom would all be
credited to a module that rendered it once — the shortfall coming out smaller
than the truth, in the direction nobody checks. It is now a maximum bipartite
matching. Measured, all 298 hypotheses match exactly one row, so the two agree
today; that is a fact, not a reason to keep computing the cheaper one.

**Guards.** 71 in `mutation_controls.py`, every one killing at least one test,
verified after each of the three landings and not only for the new ones. Five
controls added. One went dead in the making — the converse control's find-string
moved under it — and its replacement **SURVIVED** at first, because the matching
is capped by the hypothesis count and no fixture could tell a correct adjacency
from a total one. `test_two_hypotheses_from_ONE_row_represent_ONE_row` is the
shape that can: two hypotheses descending from `(= x 2)`, one as the equality and
one as the bound it entails, standing together for **one** row.

**What is left attested is 5, and each is declined on purpose.** 2 whose rendered
term is the output of a **rewrite** the file does not contain (`redand-eliminate`
folds to `bvcomp x (bvnot #b000000)`, `ext10`'s `(= a0 a0)` is constant-folded by
the arena) and would need a rewrite-step certificate — a different object and a
different check. 3 that anchoring measured as genuinely unanchorable: `ext27`
forces four leaf disequalities and a bare module does not say which, and the two
`unsat__replace_all__not-first-only` rows force none at all. These declines are
the evidence the check can fail, and none of them is fixable by weakening it.

**Next.** (1) The rewrite-step certificate is the remaining structural work and
would close 4 of the 5 (the 2 rewrite rows plus the 2 `replace_all` ones, which
are the same residue). (2) `ext27` needs the emitter to render *which* pair, i.e.
the source assertion beside the pair and an explicit assumed-entailment step.
(3) The 7 bare-pair `anchored` rows are pinned by uniqueness alone — those seven
modules are byte-identical, so each anchors against any of the others' queries.
Rendering their terms structurally, as `ArrayAxiom` and `FiniteArrayExtensionality`
both now do, would move them into the dual class and retire the weakest verdict
this checker records.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `c9223e4` | binding: the converse number says which side of the check the missing 245 rows are on — `undecomposable_spine=0` measured and gated, `represented` is a maximum matching rather than an overlap. |
| 2026-08-18 | `b9d2f0a` | binding: the 4 `FiniteArrayExtensionality` rows were never content-free — the emitter collapsed each `(select a i)`; `attested` 9 → 5, `structural` 98 → 102 with 360 new matched term nodes. |
| 2026-08-18 | `a25b18a` | binding: 66 rows were recording the weaker of two true statements — four verdicts become a partition with two-sided pins; `anchored` 10 → 73, `structural_anchored=66` new. |
