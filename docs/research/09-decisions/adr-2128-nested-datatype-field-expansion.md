# ADR-2128: nested datatype field expansion — the lever's two preconditions are ANTI-CORRELATED, and the site the probe named is not the one the representation reaches

Status: proposed
Index-summary: [ADR-2114] §4 named recursive tag/field expansion of a datatype-typed field as the repair for the `INEXACT` datatype bucket, and DT-GROUND-PROBE pointed the next build lane at it after finding **8 of 14** undecided files at `register_datatype` (`datatype_native.rs:1511-1518`). **Sizing first found the two lanes name two different sites.** `register_datatype` ALREADY walks into a `Sort::Datatype` field (`:1508-1511`); its refusal fires on the first non-datatype, non-expanding sort in the closure, which on the probe's bucket is `(Array Int <datatype>)` on **8 of 8** files and **142 of 142** refused sorts across that population -- depth unrolling reaches none of it, as [ADR-2114] §4 itself says about the `W1` arm. And where the target bucket IS the blocker, `QF_DT`, the field closure is CYCLIC on **29 of 29** undecided files (`nat = succ(pred nat)`, `list = cons(car tree, cdr list)`, blocksworld's `Tower` reached through a non-recursive `Record`), so no finite unrolling of them is exact and the lever converts 0. What the lever DOES reach is the ACKERMANN EXACTNESS PRECONDITION rather than the `==` encoding -- a different and larger population: **55 of 82** undecided `AUFDTLIRA`, **29 of 57** `UFDTLIRA`, **39 of 127** datatype-declaring `UFDT` files are CLEAN (a convertible datatype, no cyclic and no `W1`-refused datatype anywhere in the file), 410/315/158 datatypes against 0 of 96 in `QF_DT`. THE `==` ENCODING IS NOT WHERE THE GAP IS, which is the most useful thing about the existing code this lane found and makes [ADR-2114] §4's framing half true: `expand_datatype_equalities` already compares one nesting level and `unfold_traversals` already gives it children, so a free-variable `a != b` is decided with the lever OFF; the discriminator is [ADR-2114]'s own `repro/ground.smt2` UF-congruence shape, which OFF refuses BY NAME and ON answers `unsat`. THE REFERENCES: neither builds an expansion variable per field and neither bounds depth -- cvc5's member map is `d_selector_apps` (`theory_datatypes.h:145-146`, not `d_sels`, which is gone: control `grep -rn d_sels src/` = 6, all in strings) and `collectTerms` is the generic `Theory::collectTerms` (`theory.cpp:356-382`) with NO sort test; a nested field becomes one `APPLY_SELECTOR` per field with no branch on its sort (`theory_datatypes_utils.cpp:43-57`) and unrolling is gated on DEMAND (`theory_datatypes.cpp:1932-1948`, "if there are no selectors for this equivalence class, and its possible values are infinite, then do not split"), with acyclicity a colour-marked DFS over EXISTING constructor terms (`:1735-1808`) and depth/unroll/fuel/sizeBound all 0 against controls of 2/5/17/37; z3 the same, `apply_sort_cnstr:432-436` ("If s is an infinite sort, then it is not necessary to create a theory variable"), depth 0 against `mk_var` 9 / `is_datatype` 23 / `occurs_check` 11, and [ADR-2114]'s recorded lines re-verified (`:140`, `:167`, `:1009` called at `:765` CONFIRMED; `internalize_term` MOVED to `:315-405` and its "we must create a theory variable for each argument that has sort datatype" comment to `:332`). So OUR eager expansion needs a bound where both references need none, and what is copyable is the DEMAND rule -- the materialiser is seeded from the EQUALITY SITES, not from every declared variable. SHIPS OFF (`AXEYUM_DT_NESTED_FIELD_DEPTH`, default 0, clamped at 8, both bounds registered in `config_registry.rs` along with `MAX_ACK_PAIRS`, unregistered since [ADR-1935] because `datatype_native.rs` is not in `GOVERNED_FILES`): one depth-aware `datatype_expansion_is_exact_to_depth` whose `k == 0` is the pre-change predicate verbatim and which terminates on its OWN decreasing budget, so no detector is load-bearing for soundness; `materialize_nested_children` reusing `unfold_traversals`'s child NAMES so a slot that is both traversed and compared is one child; `nested_child_eq` recursing on a budget one smaller. Exactness is load-bearing for `unsat` through exactly ONE route -- the congruence antecedent, whose weakening is the [ADR-1920] shape -- and not at all for `sat`, which the replay against the original assertions checks unconditionally. [ADR-1942]'s `reject_datatype_constructor_argument` fence is deliberately NOT lifted: its doc comment demanded that a future widening "trip over a refusal rather than silently produce one", and it does. 16 tests, 8 of them a new pre-push-gated suite whose OFF arm asserts the refusal AND ITS WORDING so the ON arm's success cannot be explained by something else, with soundness-negative fixtures at several depths on both sides including two symbols sharing a child COORDINATE that must not share a child VARIABLE; the cyclic-guard tests COUNT CHILDREN rather than assert a verdict, because the guard is a cost decision resting on a soundness fact established independently and a verdict assertion would survive its deletion. **PROPOSED, NOT ACCEPTED: no default moved.** The lever ships OFF and the ship criterion (0 stable losses, 0 flips, >=1 stable gain, on the pinned list AND the held-out draw) is not met -- the interleaved A/B reached 82 of 200 `AUFDTLIRA` files on its first run (1 gain, 0 losses, 0 flips; the mover rechecked 3x per arm and agreeing with both the file's `:status` and `z3 -T:60`), and `UFDTLIRA`, `QF_DT` and the held-out draw have not run. `accepted` is reserved for a default that moved under the criterion.
Index-status: proposed
Date: 2026-09-16

## Context

[ADR-2114] §4 named the representation our ground datatype theory lacks —
**recursive tag/field expansion of a datatype-typed field, to the datatype's own
finite nesting depth, reusing the child slots `unfold_traversals` already
creates** — and sized its termination on one population: 0 of 134 files declares
a recursive datatype, deepest nest 5. It declined to build the lever, because at
most 1 of 79 undecided `AUFDTLIRA` originals is convertible by z3's own
both-engines-off arm.

`DT-GROUND-PROBE` (`bench-results/dt-ground-probe-20260916/`) then built an
independent population — 83 files with their quantified assertions stripped, all
`sat` for z3 — and found **8 of 14** undecided files terminating at
`register_datatype` (`datatype_native.rs:1511-1518`), the largest bucket, and
pointed the next build lane at ADR-2114 §4's representation.

This lane was dispatched to build it. **Sizing first found that the two lanes
name two different sites**, and that the representation's two preconditions
point at different divisions.

## Decision

> **STATUS IS `proposed`, AND THAT IS SET BY THE CRITERION RATHER THAN BY
> CONFIDENCE.** `accepted` is for an ADR whose default MOVED under the ship
> criterion: 0 stable losses, 0 flips, and at least one stable gain, on the
> pinned list AND the held-out draw. Nothing here moved a default -- the lever
> ships OFF -- and the A/B is partial. §5b carries the numbers. This flips to
> `accepted` only when the criterion is met, never because the code landed.

**The lever is built, it is OFF by default, and its reach is a shape count
rather than a verdict count until the A/B says otherwise.** Four things are
decided here.

1. **`register_datatype` does not refuse a datatype-typed field, so the
   probe's largest bucket is out of this representation's reach.** The refusal
   is array-of-datatype, 8 of 8 in that bucket and 142 of 142 across the whole
   probe population.
2. **Where the representation's target bucket IS the blocker — `QF_DT` — the
   field closure is CYCLIC on 29 of 29 undecided files**, so no finite
   unrolling of it is exact and the lever converts none of them.
3. **What the lever does reach is the ACKERMANN EXACTNESS PRECONDITION**, not
   the `==` encoding, and that is a different and larger population: 55 of 82
   undecided `AUFDTLIRA` files, 29 of 57 `UFDTLIRA`, 39 of 127
   datatype-declaring `UFDT`.
4. **The depth bound is what makes this terminate, and no detector is load
   bearing for soundness.** `datatype_expansion_is_exact_to_depth` decreases its
   own budget and answers `false` for a cyclic closure at every depth. The
   cyclic-closure detector exists to stop the materialiser spending a budget it
   cannot be paid for — a COST guard, and its test counts children rather than
   asserting a verdict, because a verdict assertion would survive its deletion.

## 1. Sizing — the two sites are not the same site

`register_datatype` (`crates/axeyum-solver/src/datatype_native.rs:1491`) already
**walks into** a `Sort::Datatype(inner)` field (`:1508-1511`). The refusal at
`:1511-1518` fires on the first non-datatype, non-expanding sort anywhere in the
closure. So a datatype-typed field is not what it refuses, and depth unrolling
does not change what it does.

Measured on the probe's own 8 undecided files, with [ADR-2114]'s `dtshape.py`
(`w1_sort`), because the predicate is decided by SORTS and is invisible in the
text of a `declare-datatypes` form:

| refused field sort | files |
|---|---:|
| `(Array Int us_rep1)` | 5 |
| `(Array Int us_rep)` | 3 |
| a bare datatype field | **0** |

and over the whole 83-file probe population, **142 of 142** refused sorts are
`(Array Int <datatype>)`. [ADR-2114] §4 says this in its own words — "`W1` is a
different shape and depth unrolling does not reach it" — and the brief that
cited the probe's largest bucket read past it.

## 1a. And where the target bucket IS the blocker, the closure is cyclic

`bench-results/board-ab-20260915/QF_DT.tsv` has 29 undecided files.
`dtshape.py` predicts `W3` — the `INEXACT` bucket, exactly this
representation's target — on **29 of 29**. And `expansion-reach.py` finds a
cyclic datatype-field closure on **29 of 29**:

```
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))))
```

and blocksworld's `Tower = stack(top Enum, rest Tower) | empty` reached through
`Record_left_center_right(left Tower, center Tower, right Tower)` — a record
that is not itself recursive but whose closure is.

**So the two conditions the representation needs point at different divisions.**
An acyclic closure, so the unrolling terminates; and no surviving non-expanding
sort, so `register_datatype` still admits. Where one holds the other tends not
to.

## 1b. The reach census, seven populations, per DATATYPE and per FILE

`bench-results/dt-field-expansion-20260916/expansion-reach.py` scores every
declared datatype on three predicates and the intersection of all three:

| population (undecided) | files | any cyclic | any W1 | ≥1 convertible dt | CLEAN |
|---|---:|---:|---:|---:|---:|
| `QF_DT` (board-ab-20260915) | 29 | **29** | 0 | **0** | **0** |
| `AUFDTLIRA` (postmerge-dt-0913) | 82 | 0 | 12 | 67 | **55** |
| `UFDTLIRA` (postmerge-dt-0913) | 57 | 0 | 0 | 29 | **29** |
| `UFDT` (postmerge-dt-0913) | 150 | 73 | 0 | 51 | **39** |
| [ADR-2114] cores-55 | 55 | 0 | 8 | 49 | 41 |
| [ADR-2114] originals-79 | 79 | 0 | 12 | 64 | 52 |
| `DT-GROUND-PROBE` stripped-83 | 83 | 0 | 13 | 73 | 60 |

`CLEAN` means the file has a convertible datatype **and** no cyclic and no
W1-refused datatype anywhere in it, so the lever is not blocked by something
else in the same file. Per datatype: `AUFDTLIRA` 410 of 1717, `UFDTLIRA` 315 of
972, `UFDT` 158 of 760, `QF_DT` 0 of 96.

Two denominators to read carefully. `UFDT`'s datatype-row denominator is **127,
not 150** — 23 of those files declare no datatype at all (one has 126
`declare-sort`s and zero `declare-datatypes`). And **this is a SHAPE count, not
a verdict count**: whether a convertible shape moves a verdict is what §5's A/B
measures, and a board TSV is a snapshot whose undecided set may have moved.

**NON-VACUITY.** A predicate that scored 0 everywhere would be
indistinguishable from a broken one, so `lever_converts` carries three
committed controls (`repro/controls.list`,
`census/reach-controls.tsv`): it FIRES on [ADR-2114]'s own
`repro/ground.smt2` (`outer`, a depth-1 record nest) and does NOT fire on
either negative — `repro/control-recursive.smt2` (cyclic) or this lane's
`repro/control-arraydt.smt2` (the `(Array Int inner)` W1 shape).

## 2. What the references do, at `file:line`

Read from the shipped sources, every negative carrying a positive control in
the same file.

**Neither reference builds an expansion variable per field, and neither bounds
unrolling depth.** Both make the nested field a TERM that joins the congruence
closure, and gate further unrolling on DEMAND.

**cvc5** (`references/cvc5/src/theory/datatypes/theory_datatypes.cpp`, 2212
lines). The member map is **not** `d_sels` — that name is gone from datatypes
(0 hits; the positive control `grep -rn "d_sels" src/` returns 6, all in
`theory/strings/type_enumerator`). It is `NodeUIntMap d_selector_apps`
(`theory_datatypes.h:145`) plus `d_selector_apps_data` (`h:146`) and an
`EqcInfo::d_selectors` bit (`h:95`), written in `addSelector` (`cpp:908`,
`:931-941`) from `eqNotifyNewClass` (`cpp:467-472`). `collectTerms` is likewise
not in the datatypes theory (0 hits; control `grep -rn "collectTerms" src/` = 12
elsewhere) — it is the generic `Theory::collectTerms`
(`src/theory/theory.cpp:356-382`), a model-building DFS with **no sort test at
all**: a `Tower`-sorted `sel_left(x)` is inserted like any other term.

A nested field is instantiated, not expanded: `instantiate` (`cpp:1367`) fires
only once a tester already holds (`:1371-1375`), and
`utils::getInstCons` (`theory_datatypes_utils.cpp:43-57`) emits **one
`APPLY_SELECTOR` per field with no branch on the field's sort**. Termination is
`checkSplit`'s guard, `theory_datatypes.cpp:1932-1948` — "if there are no
selectors for this equivalence class, and its possible values are infinite, then
do not split" (`:1912-1917`). Acyclicity is `checkCycles` (`cpp:1446`) driving
`searchForCycle` (`cpp:1735-1808`), a colour-marked DFS over **existing**
constructor terms with no depth counter. Depth bound: **none** — `maxDepth`,
`unroll`, `fuel`, `sizeBound` all 0 in that file against controls `checkSplit`
= 2, `APPLY_SELECTOR` = 5, `InferenceId::DATATYPES` = 17, `d_im\.` = 37.

**z3** (`references/z3/src/smt/theory_datatype.cpp`, 1417 lines).
[ADR-2114]'s line numbers, re-verified: `assert_is_constructor_axiom` **:140**
(confirmed), `assert_accessor_axioms` **:167** (confirmed), `occurs_check`
**:1009** called at **:765** under `m_util.is_recursive(s)` (confirmed).
`internalize_term` has **moved** to `:315-405`, its comment "we must create a
theory variable for each argument that has sort datatype" to **:332**, and the
loop giving a nested field's enode its own theory var to **:354-378**. The
array projection to `default` is at **:358-364** (with a new finite-set branch
at `:365-371` that was not in the recorded note), and the `select`-parent walk
at **:923-927** / **:992-1000**, both uses acyclicity or conflict explanation
only. The demand gate is `apply_sort_cnstr` `:432-436` — "If s is an infinite
sort, then it is not necessary to create a theory variable." Depth bound:
**none** (`depth`/`unroll`/`max_depth`/`fuel` all 0, `bound` = 1 and it is
`mk_bounded_pp`; controls `mk_var` = 9, `m_util.is_datatype` = 23,
`occurs_check` = 11).

**Ours.** `build_sym_vars` (`datatype_native.rs:1649` pre-change) gives a
datatype-typed field no variable; `build_dt_eq` skips it, which makes
`all_exact` false and the whole `==` one-directional;
`datatype_expansion_is_exact` (`:1576` pre-change) is one level deep and false
for any nested record; and that predicate is the guard on the Ackermann
congruence arms (`:904`, `:963`).

**The consequence for the design.** Our expansion is EAGER where both
references are lazy, so we need a bound where they need none, and the bound
must be the one thing the exactness predicate agrees with. What we can copy is
the DEMAND rule: the materialiser is seeded from the EQUALITY SITES, not from
every declared variable — the same move as cvc5's `d_selectors` gate and z3's
infinite-sort gate.

## 3. What ships

Behind `AXEYUM_DT_NESTED_FIELD_DEPTH` (and `NestedFieldExpansionGuard` for a
test, because a test passing only under an ambient env var is a gate on one
shell). **Default 0 — OFF.** Clamped at `MAX_NESTED_FIELD_DEPTH = 8`; an
unparseable value is OFF, never an arm nobody chose. Both bounds are registered
in `config_registry.rs`, and so is `MAX_ACK_PAIRS`, which had stood unregistered
since [ADR-1935] because `datatype_native.rs` is not in `GOVERNED_FILES` and no
coverage test could ever have asked for it.

- **`datatype_expansion_is_exact_to_depth(dt, k)`** — the one predicate, depth
  aware. `k == 0` is the pre-ADR-2128 predicate verbatim.
- **`datatype_field_closure_is_cyclic(dt)`** — [ADR-2114]'s detector, following
  MUTUAL cycles as well as self-fields.
- **`materialize_nested_children`** — one child datatype variable per
  (compared symbol, constructor, datatype-typed field), to the budget, **under
  the same `!dt_child_{sym}_{ctor}_{field}` name `unfold_traversals` uses**, so
  a slot that is both traversed and compared is ONE child (`declare_internal` is
  idempotent by name). Refuses above `MAX_NESTED_CHILDREN`, never truncates.
- **`build_dt_eq` / `build_dt_eq_restriction`** compare a datatype-typed field
  through `nested_child_eq`, which recurses on a budget one smaller and
  memoises on `(left, right, depth)`.

## 4. What "exact" means here, and why the `unsat` rests on it

> **`datatype_expansion_is_exact_to_depth(D, k)` holds iff, for two `D`
> variables materialised to depth `k`, the encoded `==` term is EQUIVALENT to
> structural equality — a biconditional, not a one-directional relaxation.**

By induction on `k`. At `k = 0` the predicate is "every field sort expands", so
every field has a variable, and `build_dt_eq` emits both the necessary clauses
(`e → tags equal`; `e ∧ tag = j → j's fields agree`) and, for every exact
constructor, the sufficiency clause — whose conjunction is exactly
`e ↔ (tags equal ∧ per-tag fields agree)`. At `k > 0` a datatype-typed field's
conjunct is the two children's own `==` term, a biconditional for the children
by the induction hypothesis, and the children ARE the field values under
`project_slot`, which reads `links[(sym, tag, i)]`. Every other field has a
variable. So the whole is structural equality again.

**Both model directions, and which one the soundness argument actually needs.**

- *Original → expanded.* From a model of the original, set `tag_o` to `o`'s
  constructor index, each scalar field variable to the field's value (a
  non-active field variable is free — [ADR-1930] — so any value does), and each
  child variable, recursively, to the field's value. Every emitted clause holds.
- *Expanded → original.* `project_slot` rebuilds `o = c_{tag_o}(…)`, scalar
  fields from their variables and datatype fields from their children
  recursively, `well_founded_default` where no child exists. **And then the
  candidate is REPLAYED against the original assertions with the ground
  evaluator before any `sat` is returned**, so a returned `sat` is a model of
  the original unconditionally, whatever the encoding did. A replay failure is
  `unknown`, never a wrong answer.

So the `sat` direction does not rest on exactness at all — the replay is the
checker. **Exactness is load-bearing for `unsat`, and through exactly one
route**: the Ackermann congruence clause `(⋀ᵢ aᵢ = bᵢ) → (w_p = w_q)` is sound
only if the encoded antecedent is not WEAKER than real equality, because a
weaker antecedent makes the implication STRONGER than the true axiom — the
[ADR-1920] shape that shipped a wrong `unsat` as [ADR-1930]. Widening the
predicate is therefore the whole soundness surface of this change, and the
materialiser must build exactly what the predicate claims. They are written to
walk `Sort::Datatype` on the same budget, both stop at zero, and both refuse to
descend a cyclic closure.

**The fence [ADR-1942] left is deliberately NOT lifted.**
`reject_datatype_constructor_argument` refuses a datatype-sorted CONSTRUCTOR
ARGUMENT in a congruence antecedent, and its doc comment says a future widening
of the exactness predicate "must trip over a refusal rather than silently
produce one". This is that widening, and the refusal stays: the free-variable
argument path (`congruence_arg_eq`'s `(None, None)` arm) goes through
`build_dt_eq` and is now exact; the constructor-application path still declines.
That is a decline, not a wrong answer, and it is one refusal this lane chose not
to earn.

## 4a. The three wrong guesses about the discriminating query

Recorded because each cost a build-test cycle and each is a real property of
the code:

1. **`a = mk_outer(mk_inner(1), 7)` is folded EXACTLY** by `simplify_datatypes`
   (read-over-construct) before the tag/field expansion runs, so a query written
   with constructor terms is decided with the lever OFF.
2. **`a != b` over two free variables agreeing on every reachable scalar is
   ALSO decided with the lever OFF**, because `expand_datatype_equalities`
   already rewrites a top-level `==` into the per-constructor field comparison
   one level deep and `unfold_traversals` turns the resulting nested `select`s
   into children. **The `==` encoding is not where the gap is** — which is the
   most useful thing this lane learned about the existing code, and it means
   [ADR-2114] §4's framing ("what our ground theory lacks is exact equality on a
   datatype-typed field") is half true: the EQUALITY is already handled one
   level deep; the PREDICATE is not.
3. The gap is the **exactness predicate consulted before any of that runs**
   (`:904`, `:963`), so the discriminating query is
   `(declare-fun f (Outer) Int) (assert (= a b)) (assert (not (= (f a) (f b))))`
   — [ADR-2114]'s own `repro/ground.smt2`. The OFF arm refuses it by name
   ("congruence over a datatype argument whose expansion is not exact"); the ON
   arm answers `unsat`.

## 5. The OBSERVED blocker census, and what it says the lever is worth

The §1b table is a SHAPE count. This is the observed one: all **318 undecided
files** of the four DT divisions, `--trace` at 24 s on s7 pinned cores 5 and 6,
bucketed by the code site the give-up sentence NAMES — a substring of the raw
detail, never a bucket label, because [ADR-2020]'s census reported one cause
where the raw details held four, and this lane's own first reading of
DT-GROUND-PROBE's largest bucket was wrong about which sort was refused.

| terminal site | n | CLEAN |
|---|---:|---:|
| `quant:ematching` | 101 | 26 |
| `quant:watchdog` | 53 | 38 |
| **`dt:exactness-result` (`:904`)** | **40** | 4 |
| `quant:time-budget` | 31 | 21 |
| **`dt:relaxation-incomplete`** | **29** | 0 |
| `quant:instantiation-sat` | 14 | 0 |
| **`dt:exactness-arg` (`:963`)** | **12** | 6 |
| `backend:sort-mismatch` | 7 | 7 |
| `bv:datatype-sorted-term` | 7 | 4 |
| `dt:ack-pair-bound` | 6 | 6 |
| `dt:model-lacks-field` | 5 | 1 |
| `quant:mbqi-unsupported` | 4 | 4 |
| `dt:field-sort-W1` | 2 | 0 |
| `quant:mbqi-rounds` | 1 | 0 |

**0 unmatched sentences**, and the classifier prints any it cannot match rather
than folding them into a catch-all — a catch-all absorbs new items and reports a
stable number that is stably wrong.

The three ADR-2128 buckets are **81 of 318 (25.5 %)**. `CLEAN` is **10 of those
81**, and is a LOWER bound: 23 undecided rows have no reach row because the
file declares no datatype at all, and the join prints that warning rather than
dropping them.

`dt:relaxation-incomplete` (29) is `project_and_replay` throwing away a `sat`
candidate because the traversed-field children are FREE. That is the
relaxation's own incompleteness, it belongs with the exactness arms, and
exactness is what would stop the children being free — but all 29 sit in files
that are cyclic or `W1`-blocked, so the lever reaches none of them.

## 5a. The lever IS live end to end, and the verdict column cannot show it

Before the A/B could be read at all, one thing had to be established: that the
arm is actually enabled at the front door. **ADR-2114's own `repro/ground.smt2`
-- the query the unit suite uses to separate the arms -- answers `unsat`
through the FRONT DOOR under BOTH arms**, because a lower rung (ADR-0022 step A
datatype elimination) decides it after `check_with_datatype_native` declines.
So a front-door A/B seeing no difference there would be indistinguishable from
an arm that was never enabled.

A real corpus file from the `dt:exactness-arg` bucket settles it
(`census/lever-endtoend-probe.txt`; binary `smtcomp_cli-arm2`, BUILD-OK at this
ADR's own commit, s7 `taskset -c 13`, 24 s; the file is
`AUFDTLIRA/.../P720-007__replay__harness.adb_13_19_assert___00.smt2`):

| arm | the give-up sentence |
|---|---|
| BASE | "**congruence over a datatype argument whose expansion is not exact** ..." |
| ARM (depth 5) | "term #1104 has sort `(Uninterpreted 6)` that the pure-Rust BV backend cannot bit-blast" |

**The exactness refusal is gone under the arm** -- the lever admitted the
Ackermann congruence it used to refuse -- and the query then died further down
on an unrelated reason. **The verdict is `unknown` under both.**

So on this population the lever MOVES THE BLOCKER without moving the verdict,
and two traps follow, both written into the artifacts rather than left to a
reader:

- A verdict-only A/B reports a perfect zero-diff that reads as "the lever does
  nothing", which is the same shape as "the arm was never enabled".
  `ab-summarize.py` therefore PRINTS A NOTE on a zero-diff instead of letting
  the zeros speak, and its exit status depends on the finding (3 on a flip, 2
  on a loss).
- The other direction is a trap too: the arm's sentence names a DIFFERENT site,
  so a census keyed on the give-up wording would report the lever as having
  "moved 52 files out of the datatype bucket" when what it did was hand them to
  the next rung. Moving a blocker is progress only if the next rung can do
  something with it; on this file it cannot.

## 5b. The A/B, PARTIAL -- and no ship decision

**The interleaved A/B did not complete in this lane, so no ship decision is
taken and the lever stays OFF -- which is what it ships as.** What ran is the
first **82 of 200** `AUFDTLIRA` files (`census/ab-AUFDTLIRA-partial*`; the run
was then STOPPED BY THE COORDINATOR at 82 rows -- deliberately, on this lane's
own "harvest it or kill those PIDs" note, and recorded as a misjudgment once
the 82 rows turned out to hold the mover -- and relaunched). One binary,
two env values, the two arms back to back per file on one core, order
alternated per file, 24 s, this lane's pinned pairs on s7:

    rows=82  (base-first 40 / arm-first 42)
    base : unsat 52  unknown 30
    arm  : unsat 53  unknown 29
    GAINS 1   LOSSES 0   sat<->unsat FLIPS 0
      +unsat  O512-022__stacks__stacks.ads_84_58_index_check___00.smt2

**1 gain, 0 losses, 0 flips of 82, and no soundness incident.** The mover is
rechecked and verified (`census/mover-O512-022-stacks.txt`): stable 3 of 3 per
arm on one core, and its `unsat` agrees with the file's own
`(set-info :status unsat)` AND with `z3 -T:60` -- two sources that do not share
an origin.

**AND THE MOVER DOES NOT COME FROM THE BUCKET THIS ADR PREDICTED.** It is not
in any of §5's three datatype buckets: its census row is `quant:time-budget`
("quantified solve time budget exhausted after MBQI and the finite-model
finder", `total_ms=24577`), and under the base arm it gives up on the watchdog.
Under the arm it is `decided_by=q:mbqi-quick` in **337 ms**. So what the lever
did here was make the GROUND SUB-SOLVES INSIDE THE QUANTIFIER LOOP stronger --
`decide_instantiation`'s `check_auto` on a quantifier-free query, the path §1
of [ADR-2114] traced -- not remove a refusal and let the verdict follow.

That is recorded as observed rather than fitted to the story that preceded it.
**§1b's `CLEAN` count was built as a predictor of where gains would come from
and the one observed gain came from outside it**, so `CLEAN` must not be quoted
as a forecast of gains until something has measured that it is one. One mover
is one mover.

It is a PARTIAL and it is labelled as one: 82 of 200 in one of three divisions
is not a division result, `UFDTLIRA` and `QF_DT` did not run at all, and the
held-out draw did not happen. The runner (`ab-run.sh`), the summariser
(`ab-summarize.py`, whose exit status depends on the finding) and the three
200-file lists are committed, so the measurement is a re-run rather than a
re-derivation.

[ADR-2020]: adr-2020-giveup-census-buckets.md

## Tests

`crates/axeyum-solver/tests/dt_nested_field_2128.rs` (8 tests, in the pre-push
dispatch/reason block) and `datatype_native::nested_field_tests` (8 unit tests).

The OFF/ON pair is the non-vacuity control:
`off_arm_refuses_the_nested_congruence` asserts the refusal AND its wording, so
a refusal for some other reason cannot leave the ON arm's success unexplained.
Soundness-negative fixtures run at several depths on both sides —
`sound_two_distinct_nested_values_do_not_collide` (two symbols sharing the child
COORDINATE `(0,0)` must not share the child VARIABLE),
`sound_nested_congruence_does_not_force_equal_results` (the [ADR-1920] shape),
`sound_nested_selector_injectivity_is_never_contradicted`, and two on a cyclic
datatype.

The cyclic-guard unit tests **count children rather than assert a verdict**,
and that is the point: the guard is a cost decision resting on a soundness fact
established independently, so a verdict assertion would survive its deletion and
prove nothing.

**The mutation suite `dt-nested-field-2128`: both guards kill EXACTLY ONE test,
and they are DIFFERENT tests** (`census/mutation-dt-nested-field-2128.txt`):

| guard deleted | the test that died |
|---|---|
| the materialiser skips a CYCLIC field closure | `the_cyclic_guard_builds_no_children_for_a_cyclic_datatype` |
| the exactness predicate recurses into the nested field | `exactness_widens_with_the_budget_and_never_for_a_cycle` |

`--check-anchors` reports `suites=150 anchors=1100 stale=0`.

**The first mutant for the second guard was not usable, and that is worth
recording.** Deleting the `depth > 0 &&` conjunct reported `INCONSISTENT -- 1
test binaries started but 0 reported a result`: without the budget check the
predicate DIVERGES on a cyclic datatype and takes the binary down. A crash is a
kill in the crudest sense and it names nothing, so the registered mutant keeps
the budget and drops the RECURSION instead, which terminates and is wrong.

[ADR-1920]: adr-1920-datatype-native-capability-gate.md
[ADR-1930]: adr-1930-unspecified-selector-reads-are-free.md
[ADR-1935]: adr-1935-datatype-field-sorts-and-ackermann-congruence.md
[ADR-1942]: adr-1942-constructor-arguments-in-congruence-antecedents.md
[ADR-2114]: adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md
